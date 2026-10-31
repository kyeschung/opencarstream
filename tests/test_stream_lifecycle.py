"""Tests for stream reuse / stop logic and the yt-dlp resolve path.

Run from the repo root:
    python3 -m unittest discover -s tests -v

No network access is needed. A fake `yt-dlp` script is put first on PATH;
the end-to-end test additionally needs ffmpeg (skipped if missing).
"""

import os
import shutil
import stat
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from functools import partial
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from unittest import mock

os.environ.setdefault("STREAM_WIDTH", "320")
os.environ.setdefault("STREAM_HEIGHT", "180")
os.environ.setdefault("MJPEG_FPS", "10")
os.environ.setdefault("MAX_STREAMS", "3")

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import server  # noqa: E402


class FakeProc:
    """Stands in for a Popen object so stop() can be observed."""

    def __init__(self):
        self.terminated = False
        self.returncode = None

    def poll(self):
        return self.returncode

    def terminate(self):
        self.terminated = True
        self.returncode = -15

    def kill(self):
        self.terminate()

    def wait(self, timeout=None):
        return self.returncode


def _write_fake_ytdlp(directory: str, body: str) -> None:
    path = os.path.join(directory, "yt-dlp")
    with open(path, "w") as f:
        f.write("#!/bin/sh\n" + body + "\n")
    os.chmod(path, os.stat(path).st_mode | stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH)


class RegistryReuseTests(unittest.TestCase):
    def setUp(self):
        self.reg = server.Registry()

    def test_same_client_same_video_while_starting_is_reused(self):
        s1, reused1 = self.reg.acquire("mjpeg|A|q=|seek=0", "A", owner="car")
        s2, reused2 = self.reg.acquire("mjpeg|A|q=|seek=0", "A", owner="car")
        self.assertFalse(reused1)
        self.assertTrue(reused2)
        self.assertIs(s1, s2)
        self.assertEqual(len(self.reg.all_streams()), 1)

    def test_reused_while_ffmpeg_running_but_no_frame_yet(self):
        s1, _ = self.reg.acquire("k", "A", owner="car")
        s1.status = "streaming"          # ffmpeg spawned, no frame yet
        s2, reused = self.reg.acquire("k", "A", owner="car")
        self.assertTrue(reused)
        self.assertIs(s1, s2)

    def test_switching_video_stops_old_stream_and_kills_procs(self):
        old, _ = self.reg.acquire("k-old", "A", owner="car")
        yt, ff = FakeProc(), FakeProc()
        old._yt_proc, old._ff_proc = yt, ff
        new, reused = self.reg.acquire("k-new", "B", owner="car")
        self.assertFalse(reused)
        self.assertIsNot(old, new)
        self.assertTrue(old.stopped)
        self.assertEqual(old.status, "done")
        self.assertTrue(yt.terminated and ff.terminated)
        self.assertEqual([s.id for s in self.reg.all_streams()], [new.id])

    def test_other_clients_streams_are_left_alone(self):
        theirs, _ = self.reg.acquire("k1", "A", owner="other-car")
        mine, _ = self.reg.acquire("k2", "B", owner="car")
        self.assertFalse(theirs.stopped)
        self.assertEqual(len(self.reg.all_streams()), 2)
        # Same key but different owner must not be shared either.
        mine2, reused = self.reg.acquire("k1", "A", owner="car")
        self.assertFalse(reused)
        self.assertIsNot(mine2, theirs)
        self.assertFalse(theirs.stopped)
        self.assertTrue(mine.stopped)

    def test_live_stream_is_restarted_not_reused(self):
        s1, _ = self.reg.acquire("k", "A", owner="car")
        s1.status = "streaming"
        s1.first_frame_at = time.time()
        s2, reused = self.reg.acquire("k", "A", owner="car")
        self.assertFalse(reused)
        self.assertIsNot(s1, s2)
        self.assertTrue(s1.stopped)

    def test_errored_stream_is_replaced(self):
        s1, _ = self.reg.acquire("k", "A", owner="car")
        s1.status = "error"
        s2, reused = self.reg.acquire("k", "A", owner="car")
        self.assertFalse(reused)
        self.assertIsNot(s1, s2)
        self.assertEqual(s1.status, "error")   # error kept for diagnostics

    def test_reuse_disabled_always_creates(self):
        s1, _ = self.reg.acquire("k", "A", owner="car", reuse=False)
        s2, reused = self.reg.acquire("k", "A", owner="car", reuse=False)
        self.assertFalse(reused)
        self.assertTrue(s1.stopped)
        self.assertIsNot(s1, s2)

    def test_capacity_evicts_least_recently_used(self):
        with mock.patch.object(server, "MAX_STREAMS", 2):
            a, _ = self.reg.acquire("k1", "A", owner="c1")
            b, _ = self.reg.acquire("k2", "B", owner="c2")
            a.last_used = time.time() - 100
            c, _ = self.reg.acquire("k3", "C", owner="c3")
        self.assertTrue(a.stopped)
        self.assertFalse(b.stopped)
        self.assertEqual({s.id for s in self.reg.all_streams()}, {b.id, c.id})

    def test_find_reusable(self):
        s1, _ = self.reg.acquire("k", "A", owner="car")
        self.assertIs(self.reg.find_reusable("k", "car"), s1)
        self.assertIsNone(self.reg.find_reusable("k", "someone-else"))
        self.assertIsNone(self.reg.find_reusable("other", "car"))


class StreamStateTests(unittest.TestCase):
    def test_ensure_pipeline_starts_once(self):
        stream = server.Stream("s-test", "A")
        calls = []
        with mock.patch.object(server, "run_pipeline", side_effect=lambda s: calls.append(s)):
            results = [stream.ensure_pipeline() for _ in range(5)]
            time.sleep(0.1)
        self.assertEqual(results.count(True), 1)
        self.assertEqual(len(calls), 1)

    def test_ensure_pipeline_not_started_after_stop(self):
        stream = server.Stream("s-test", "A")
        stream.stop()
        with mock.patch.object(server, "run_pipeline") as rp:
            self.assertFalse(stream.ensure_pipeline())
            time.sleep(0.05)
            rp.assert_not_called()

    def test_stage_progression(self):
        stream = server.Stream("s-test", "A")
        self.assertEqual(stream.stage, "queued")
        stream.set_stage("resolving")
        self.assertEqual(stream.to_dict()["stage"], "resolving")
        stream.set_stage("starting")
        self.assertEqual(stream.stage, "starting")
        stream.first_frame_at = time.time()
        self.assertEqual(stream.stage, "live")
        stream.status = "error"
        self.assertEqual(stream.stage, "error")

    def test_attach_proc_after_stop_kills_it(self):
        stream = server.Stream("s-test", "A")
        stream.stop()
        proc = FakeProc()
        self.assertFalse(stream.attach_proc("_yt_proc", proc))
        self.assertTrue(proc.terminated)


class ResolveHelpersTests(unittest.TestCase):
    def test_parse_resolve_output(self):
        out = "29.97\tMy Video\nhttps://cdn.example/v.mp4\n"
        self.assertEqual(
            server._parse_resolve_output(out),
            {"url": "https://cdn.example/v.mp4", "title": "My Video", "fps": 29.97},
        )

    def test_parse_resolve_output_na_fields(self):
        info = server._parse_resolve_output("NA\tNA\nhttps://cdn.example/v.mp4\n")
        self.assertEqual(info, {"url": "https://cdn.example/v.mp4", "title": "", "fps": None})

    def test_parse_resolve_output_title_with_tab_and_no_urls(self):
        info = server._parse_resolve_output("30\tA\tB\nhttps://x/1\nhttps://x/2\n")
        self.assertEqual(info["title"], "A\tB")
        self.assertEqual(info["url"], "https://x/1")
        self.assertIsNone(server._parse_resolve_output("30\tOnly a title\n"))
        self.assertIsNone(server._parse_resolve_output(""))

    def test_resolve_cache_ttl_and_invalidate(self):
        cache = server.ResolveCache(ttl_s=60)
        cache.put(("u", "f"), {"url": "x"})
        cache.put(("u", "audio:f"), {"url": "y"})
        cache.put(("other", "f"), {"url": "z"})
        self.assertEqual(cache.get(("u", "f")), {"url": "x"})
        cache.invalidate("u")
        self.assertIsNone(cache.get(("u", "f")))
        self.assertIsNone(cache.get(("u", "audio:f")))
        self.assertEqual(cache.get(("other", "f")), {"url": "z"})
        expired = server.ResolveCache(ttl_s=60)
        expired.put(("u", "f"), {"url": "x"})
        with mock.patch.object(server.time, "time", return_value=time.time() + 120):
            self.assertIsNone(expired.get(("u", "f")))

    def test_youtube_thumb(self):
        self.assertEqual(
            server._youtube_thumb("https://www.youtube.com/watch?v=dQw4w9WgXcQ&t=1"),
            "https://i.ytimg.com/vi/dQw4w9WgXcQ/hqdefault.jpg",
        )
        self.assertEqual(
            server._youtube_thumb("https://youtu.be/dQw4w9WgXcQ"),
            "https://i.ytimg.com/vi/dQw4w9WgXcQ/hqdefault.jpg",
        )
        self.assertEqual(server._youtube_thumb("https://www.twitch.tv/foo"), "")

    def test_js_json_cannot_break_out_of_script(self):
        out = server._js_json({"t": "</script><script>alert(1)</script>"})
        self.assertNotIn("</script>", out)
        self.assertNotIn("<", out)


class FakeYtDlpTests(unittest.TestCase):
    """Exercise the real subprocess path with a fake yt-dlp on PATH."""

    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self._old_path = os.environ.get("PATH", "")
        os.environ["PATH"] = self.tmp + os.pathsep + self._old_path
        server.resolve_cache.invalidate("https://example.test/watch?v=slow")
        server.resolve_cache.invalidate("https://example.test/watch?v=ok")

    def tearDown(self):
        os.environ["PATH"] = self._old_path
        shutil.rmtree(self.tmp, ignore_errors=True)

    def test_stop_kills_slow_ytdlp(self):
        _write_fake_ytdlp(self.tmp, "exec sleep 30")
        stream = server.Stream("s-slow", "https://example.test/watch?v=slow")
        result = {}

        def run():
            result["value"] = server._ytdlp_resolve(stream, "best")

        t = threading.Thread(target=run)
        t0 = time.time()
        t.start()
        for _ in range(100):
            if stream._yt_proc is not None:
                break
            time.sleep(0.02)
        self.assertIsNotNone(stream._yt_proc, "yt-dlp should be registered on the stream")
        stream.stop()
        t.join(timeout=6)
        self.assertFalse(t.is_alive())
        self.assertLess(time.time() - t0, 6)
        self.assertEqual(result["value"], (None, "stopped"))

    def test_resolve_uses_cache_on_second_call(self):
        counter = os.path.join(self.tmp, "count")
        _write_fake_ytdlp(
            self.tmp,
            f'echo x >> "{counter}"\n'
            'printf "25\\tCached Title\\nhttps://cdn.example/v.mp4\\n"',
        )
        url = "https://example.test/watch?v=ok"
        s1 = server.Stream("s-a", url)
        info, err = server._ytdlp_resolve(s1, "best")
        self.assertEqual(err, "")
        self.assertEqual(info["title"], "Cached Title")
        self.assertEqual(info["fps"], 25.0)
        s2 = server.Stream("s-b", url)
        info2, _ = server._ytdlp_resolve(s2, "best")
        self.assertEqual(info2, info)
        with open(counter) as f:
            self.assertEqual(len(f.read().split()), 1, "second resolve should hit the cache")

    def test_concurrent_audio_lookups_share_one_ytdlp(self):
        counter = os.path.join(self.tmp, "count")
        _write_fake_ytdlp(
            self.tmp,
            f'echo x >> "{counter}"\nsleep 1\necho https://cdn.example/a.m4a',
        )
        url = "https://example.test/watch?v=audio-dedupe"
        server.resolve_cache.invalidate(url)
        results = []
        threads = [
            threading.Thread(target=lambda: results.append(server._ytdlp_audio_url(url, "bestaudio")))
            for _ in range(3)
        ]
        for t in threads:
            t.start()
        for t in threads:
            t.join(timeout=10)
        self.assertEqual(results, ["https://cdn.example/a.m4a"] * 3)
        with open(counter) as f:
            self.assertEqual(len(f.read().split()), 1)

    def test_fatal_ytdlp_error_fails_fast_without_retry_flag(self):
        counter = os.path.join(self.tmp, "count")
        _write_fake_ytdlp(
            self.tmp,
            f'echo x >> "{counter}"\n'
            'echo "ERROR: [youtube] abc: Private video. Sign in if you\'ve been granted access" >&2\nexit 1',
        )
        stream = server.Stream("s-fatal", "https://example.test/watch?v=private")
        server.run_pipeline(stream)
        self.assertEqual(stream.status, "error")
        self.assertFalse(stream.retryable)
        self.assertIn("Private video", stream.error)
        with open(counter) as f:
            self.assertEqual(len(f.read().split()), 1, "no format/pipe fallbacks for a fatal error")

    def test_fatal_classifier(self):
        self.assertTrue(server._is_fatal_ytdlp_error("ERROR: [youtube] x: Video unavailable"))
        self.assertFalse(server._is_fatal_ytdlp_error("ERROR: Requested format is not available"))
        self.assertFalse(server._is_fatal_ytdlp_error("ERROR: unable to download webpage: timed out"))


@unittest.skipUnless(shutil.which("ffmpeg"), "ffmpeg not installed")
class PipelineEndToEndTests(unittest.TestCase):
    """Fake yt-dlp returns an http URL to a tiny generated mp4; the real
    ffmpeg pipeline must reach the live stage and set the title."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = tempfile.mkdtemp()
        cls.media = os.path.join(cls.tmp, "media")
        os.mkdir(cls.media)
        subprocess.run(
            ["ffmpeg", "-loglevel", "error", "-f", "lavfi", "-i",
             "testsrc=size=160x90:rate=10", "-t", "20", "-pix_fmt", "yuv420p",
             os.path.join(cls.media, "clip.mp4")],
            check=True,
        )
        class QuietHandler(SimpleHTTPRequestHandler):
            def log_message(self, *args):
                pass

        handler = partial(QuietHandler, directory=cls.media)
        cls.httpd = ThreadingHTTPServer(("127.0.0.1", 0), handler)
        threading.Thread(target=cls.httpd.serve_forever, daemon=True).start()
        cls.clip_url = f"http://127.0.0.1:{cls.httpd.server_port}/clip.mp4"
        cls.bin = os.path.join(cls.tmp, "bin")
        os.mkdir(cls.bin)
        _write_fake_ytdlp(cls.bin, f'sleep 0.3\nprintf "10\\tTest Clip\\n{cls.clip_url}\\n"')
        cls._old_path = os.environ.get("PATH", "")
        os.environ["PATH"] = cls.bin + os.pathsep + cls._old_path

    @classmethod
    def tearDownClass(cls):
        os.environ["PATH"] = cls._old_path
        cls.httpd.shutdown()
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def test_pipeline_reaches_live_and_switch_stops_it(self):
        reg = server.Registry()
        url = "https://example.test/watch?v=e2e"
        server.resolve_cache.invalidate(url)
        stream, _ = reg.acquire("mjpeg|e2e", url, owner="car")
        stages = set()
        self.assertTrue(stream.ensure_pipeline())
        deadline = time.time() + 20
        while time.time() < deadline and stream.stage != "live":
            stages.add(stream.stage)
            time.sleep(0.05)
        self.assertEqual(stream.stage, "live", stream.to_dict())
        self.assertEqual(stream.title, "Test Clip")
        self.assertTrue(stages & {"queued", "resolving", "starting"})
        ff = stream._ff_proc
        self.assertIsNotNone(ff)

        # Switching to another video kills this ffmpeg.
        with mock.patch.object(server, "run_pipeline"):
            reg.acquire("mjpeg|other", "https://example.test/watch?v=other", owner="car")
        ff.wait(timeout=5)
        self.assertIsNotNone(ff.poll())
        self.assertEqual(stream.status, "done")
        time.sleep(0.3)
        # The pipeline thread must not flip a stopped stream back to streaming.
        self.assertEqual(stream.status, "done")


if __name__ == "__main__":
    unittest.main()
