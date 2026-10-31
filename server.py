#!/usr/bin/env python3
"""
OpenCarStream MJPEG Streamer
Usage:
  http://yourserver/stream?url=https://youtube.com/watch?v=xxx
  http://yourserver/             → status page
  http://yourserver/health       → health check
"""

import re
import subprocess
import threading
import time
import sys
import os
import signal
import json
import logging
from collections import deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from http.server import HTTPServer, BaseHTTPRequestHandler
from urllib.parse import urlparse, parse_qs, unquote, quote
from urllib.request import Request, urlopen
from socketserver import ThreadingMixIn

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%H:%M:%S"
)
log = logging.getLogger("streamer")


def _parse_lang_map(raw: str) -> dict[str, str]:
    """
    Parse env mapping in format: "es:ES,en:US" or "en:8.8.8.8".
    Keys are normalized to lowercase language codes.
    """
    result: dict[str, str] = {}
    for part in (raw or "").split(","):
        item = part.strip()
        if not item or ":" not in item:
            continue
        lang, value = item.split(":", 1)
        lang = lang.strip().lower()
        value = value.strip()
        if lang and value:
            result[lang] = value
    return result


# ── Config (override via env vars) ────────────────────────────────────────────
HOST          = os.environ.get("HOST", "0.0.0.0")
PORT          = int(os.environ.get("PORT", "8080"))
MJPEG_FPS     = int(os.environ.get("MJPEG_FPS", "24"))
FFMPEG_QUALITY= int(os.environ.get("FFMPEG_QUALITY", "3"))   # 1=best, 31=worst
STREAM_WIDTH  = int(os.environ.get("STREAM_WIDTH", "1920"))
STREAM_HEIGHT = int(os.environ.get("STREAM_HEIGHT", "1080"))
MAX_STREAMS   = int(os.environ.get("MAX_STREAMS", "3"))       # concurrent stream slots
AUDIO_DELAY_MS= int(os.environ.get("AUDIO_DELAY_MS", "0"))   # ms to delay video start after audio, to keep streams in sync
LOCAL_MEDIA_VIDEO_DELAY_MS = int(
    os.environ.get("LOCAL_MEDIA_VIDEO_DELAY_MS", "1500")
)
SUBSCRIPTIONS_FILE  = os.environ.get("SUBSCRIPTIONS_FILE", "/config/subscriptions.json")
ACE_STREAMS_FILE    = os.environ.get("ACE_STREAMS_FILE", "/config/ace_streams.json")
FAVORITES_FILE      = os.environ.get("FAVORITES_FILE", "/config/favorites.json")
PROGRESS_FILE       = os.environ.get("PROGRESS_FILE", "/config/watch_progress.json")
HOME_FEED_CACHE_FILE = os.environ.get("HOME_FEED_CACHE_FILE", "/config/home_feed_cache.json")
# How many recent videos to fetch per channel for the Home feed
HOME_FEED_PER_CHANNEL = int(os.environ.get("HOME_FEED_PER_CHANNEL", "7"))
# Max concurrent yt-dlp workers when building the Home feed
HOME_FEED_WORKERS     = int(os.environ.get("HOME_FEED_WORKERS", "8"))
# Cache the Home feed for this many seconds (0 = disabled)
HOME_FEED_CACHE_SECS  = int(os.environ.get("HOME_FEED_CACHE_SECS", str(30 * 60)))
# Only show videos uploaded within this many days (0 = no filter; 0 recommended since yt-dlp
# often returns NA for upload_date in flat-playlist mode)
HOME_FEED_MAX_AGE_DAYS = int(os.environ.get("HOME_FEED_MAX_AGE_DAYS", "0"))
# Comma-separated list of Pluto TV language codes to load, e.g. "es,en"
PLUTO_LANGS         = [l.strip() for l in os.environ.get("PLUTO_LANGS", "es,en").split(",") if l.strip()]
PLUTO_REFRESH_SECS  = int(os.environ.get("PLUTO_REFRESH_SECS", str(60 * 60)))  # 1 h
PLUTO_APP_VERSION   = os.environ.get("PLUTO_APP_VERSION", "8.0.0-111b2b9dc00bd0bea9030b30662159ed9e7c8bc6")
# Maps UI language -> Pluto marketing region (country code).
# Default keeps Spanish in ES and routes English to US lineup.
PLUTO_REGION_MAP    = _parse_lang_map(os.environ.get("PLUTO_REGION_MAP", "es:ES,en:US"))
# Optional language -> X-Forwarded-For IP used for boot/channels requests.
# This helps force region-specific lineups when server IP geo differs.
PLUTO_XFF_MAP       = _parse_lang_map(os.environ.get("PLUTO_XFF_MAP", "en:8.8.8.8"))
LOCAL_MEDIA_DIR     = os.environ.get("LOCAL_MEDIA_DIR", "/media/videos")
IPTV_LISTS_DIR      = os.environ.get("IPTV_LISTS_DIR", "/iptv_lists")
MAX_STREAM_AGE_S    = int(os.environ.get("MAX_STREAM_AGE_S", str(5 * 3600)))  # stop streams older than this
# BCP-47 language tag for YouTube titles/descriptions, e.g. "es", "fr", "de".
# Leave empty ("") to use YouTube's default (usually matches the video's original language).
YT_LANG             = os.environ.get("YT_LANG", "")
LOCAL_MEDIA_EXTS    = {
    ".mp4", ".mkv", ".webm", ".avi", ".mov", ".m4v", ".mpg", ".mpeg", ".ts",
}
IPTV_LIST_EXTS      = {".m3u", ".m3u8"}


# ── Per-stream state ──────────────────────────────────────────────────────────
class Stream:
    def __init__(self, stream_id: str, url: str, quality: int | None = None):
        self.id         = stream_id
        self.url        = url
        self.quality    = quality
        self.lock       = threading.Lock()
        self.frame      : bytes | None = None
        self.status     = "starting"   # starting | streaming | error | done
        self.title      = ""
        self.error      = ""
        self.error_detail = ""
        self.created_at = time.time()
        self.last_used  = time.time()
        self._yt_proc   = None
        self._ff_proc   = None
        self._audio_proc: object | None = None   # separate audio ffmpeg for direct streams
        self.seek_s     : float = 0.0
        self.fps        : float = float(MJPEG_FPS)
        self.started_at : float | None = None
        self.first_frame_at: float | None = None
        # Audio ring-buffer for direct streams (HLS/MPEG-TS) where a second
        # connection to the source is not viable.
        self._audio_lock   = threading.Lock()
        self._audio_chunks : list[bytes] = []
        self._audio_ready  = threading.Event()
        self._audio_done   = False
        self._frame_history = deque(maxlen=max(MJPEG_FPS * 12, 120))
        self.frame_cond     = threading.Condition(self.lock)  # notified whenever a new frame arrives
        self.audio_only     = False  # when True, skip MJPEG pipeline and run audio only

    def stop(self):
        for proc in [self._ff_proc, self._yt_proc, self._audio_proc]:
            if proc:
                try:
                    proc.terminate()
                    proc.wait(timeout=3)
                except Exception:
                    pass
        self._ff_proc     = None
        self._yt_proc     = None
        self._audio_proc  = None
        with self._audio_lock:
            self._audio_done = True
        self._audio_ready.set()
        with self.frame_cond:
            self.frame_cond.notify_all()
        with self.lock:
            self._frame_history.clear()

    def to_dict(self):
        return {
            "id":     self.id,
            "url":    self.url,
            "quality": self.quality,
            "started_at": self.started_at,
            "status": self.status,
            "title":  self.title,
            "error":  self.error,
            "error_detail": self.error_detail,
            "age_s":  round(time.time() - self.created_at),
            "fps":    self.fps,
            "seek_s": self.seek_s,
        }


# ── Stream registry ───────────────────────────────────────────────────────────
class Registry:
    def __init__(self):
        self._lock    = threading.Lock()
        self._streams : dict[str, Stream] = {}
        self._counter = 0

    def _make_id(self) -> str:
        self._counter += 1
        return f"s{self._counter}"

    def get_or_create(
        self,
        url: str,
        quality: int | None = None,
        reuse_existing: bool = True,
    ) -> Stream:
        with self._lock:
            if reuse_existing:
                # Return existing live stream for same URL + quality profile
                for s in self._streams.values():
                    if (
                        s.url == url
                        and s.quality == quality
                        and s.status in ("starting", "streaming")
                    ):
                        s.last_used = time.time()
                        return s

            # Evict oldest if at capacity
            if len(self._streams) >= MAX_STREAMS:
                oldest = min(self._streams.values(), key=lambda s: s.last_used)
                log.info(f"Evicting stream {oldest.id} ({oldest.url[:60]})")
                oldest.stop()
                del self._streams[oldest.id]

            sid    = self._make_id()
            stream = Stream(sid, url, quality=quality)
            self._streams[sid] = stream
            return stream

    def get(self, sid: str) -> Stream | None:
        with self._lock:
            return self._streams.get(sid)

    def all_streams(self) -> list[Stream]:
        with self._lock:
            return list(self._streams.values())

    def cleanup_done(self):
        with self._lock:
            dead = [sid for sid, s in self._streams.items()
                    if s.status in ("error", "done")
                    and time.time() - s.last_used > 60]
            for sid in dead:
                self._streams[sid].stop()
                del self._streams[sid]
                log.info(f"Cleaned up stream {sid}")

    def cleanup_old(self):
        """Stop and remove streams that have been active longer than MAX_STREAM_AGE_S."""
        cutoff = time.time() - MAX_STREAM_AGE_S
        with self._lock:
            old = [sid for sid, s in self._streams.items()
                   if s.created_at < cutoff and s.status in ("starting", "streaming")]
            for sid in old:
                log.info(f"Auto-stopping stream {sid} (age limit reached)")
                self._streams[sid].stop()
                self._streams[sid].status = "done"
                del self._streams[sid]


registry = Registry()


# ── Pluto TV channel cache ─────────────────────────────────────────────────────
class PlutoCache:
    def __init__(self):
        self._lock  = threading.Lock()
        self._by_lang: dict[str, list[dict]] = {}
        self._errors:  dict[str, str]        = {}
        # { lang: (device_id, session_token, stitcher_params, refresh_at) }
        self._sessions: dict[str, tuple[str, str, str, float]] = {}

    def get(self, lang: str) -> tuple[list[dict], str]:
        with self._lock:
            return list(self._by_lang.get(lang, [])), self._errors.get(lang, "")

    def get_meta(self, lang: str) -> dict[str, str | int]:
        """Return metadata for a language cache entry."""
        from urllib.parse import parse_qsl
        region, xff = self._lang_context(lang)
        with self._lock:
            sess = self._sessions.get(lang)
        if not sess:
            return {"country": "", "refresh_at": 0, "region": region, "xff": xff}
        _, _token, stitcher_params, refresh_at = sess
        country = ""
        for key, val in parse_qsl(stitcher_params, keep_blank_values=True):
            if key == "country":
                country = val
                break
        return {
            "country": country,
            "refresh_at": int(refresh_at),
            "region": region,
            "xff": xff,
        }

    def langs(self) -> list[str]:
        with self._lock:
            return list(self._by_lang.keys())

    @staticmethod
    def _lang_context(lang: str) -> tuple[str, str]:
        lang_key = (lang or "").strip().lower()
        region = PLUTO_REGION_MAP.get(lang_key, lang_key.upper() or "US")
        xff = PLUTO_XFF_MAP.get(lang_key, "")
        return region, xff

    @staticmethod
    def _apply_stitcher_params(hls_url: str, stitcher_params: str, session_token: str = "") -> str:
        """Merge Pluto stitcher query params into the channel HLS URL."""
        from urllib.parse import urlsplit, urlunsplit, parse_qsl, urlencode
        parts = urlsplit(hls_url)
        # Ensure /v2 prefix on path (Pluto requires /v2/stitch/hls/...)
        path = parts.path
        if path.startswith("/stitch/") and not path.startswith("/v2/"):
            path = "/v2" + path
        merged = dict(parse_qsl(parts.query, keep_blank_values=True))
        for k, v in parse_qsl(stitcher_params, keep_blank_values=True):
            merged[k] = v
        if session_token:
            merged["jwt"] = session_token
        merged["includeExtendedEvents"] = "true"
        merged["masterJWTPassthrough"] = "true"
        query = urlencode(merged, doseq=True)
        return urlunsplit((parts.scheme, parts.netloc, path, query, ""))

    def build_channel_url(
        self, lang: str, channel_id: str, force_refresh: bool = False
    ) -> tuple[str | None, str]:
        """
        Build a fresh Pluto playback URL for channel_id in lang.
        Returns (url, err). When url is None, err describes the failure.
        """
        if not channel_id:
            return None, "missing channel id"

        if force_refresh:
            self._fetch_lang(lang)

        with self._lock:
            channels = self._by_lang.get(lang, [])
            sess = self._sessions.get(lang)
            channel = next((c for c in channels if c.get("id") == channel_id), None)

        if channel is None:
            return None, f"channel '{channel_id}' not found for lang '{lang}'"
        if not sess:
            return None, f"Pluto TV [{lang}] session unavailable"

        _, session_token, stitcher_params, _ = sess
        hls_url = channel.get("hls_url", "")
        if not hls_url:
            return None, "channel has no HLS URL"
        return self._apply_stitcher_params(hls_url, stitcher_params, session_token), ""

    def _boot(self, lang: str) -> tuple[str, str, str, int] | None:
        """Call Pluto boot API and return (device_id, session_token, stitcher_params, refresh_in_sec)."""
        import urllib.request, uuid
        region, xff = self._lang_context(lang)
        device_id = str(uuid.uuid4())
        url = (
            f"https://boot.pluto.tv/v4/start"
            f"?appName=web&appVersion={PLUTO_APP_VERSION}"
            f"&deviceDNT=0&deviceId={device_id}&deviceMake=chrome"
            f"&deviceModel=web&deviceType=web&deviceVersion=122.0.0"
            f"&clientModelNumber=1.0.0&serverSideAds=false"
            f"&drmCapabilities=widevine%3AL3&blockingMode="
            f"&marketingRegion={region}&clientID={device_id}"
        )
        try:
            headers = {
                "User-Agent": _BROWSER_UA,
                "Accept": "application/json",
                "Referer": "https://pluto.tv/",
                "Origin": "https://pluto.tv",
            }
            if xff:
                headers["X-Forwarded-For"] = xff
            req = urllib.request.Request(
                url, headers=headers
            )
            with urllib.request.urlopen(req, timeout=15) as resp:
                raw = resp.read().decode()
                data = json.loads(raw)
        except urllib.error.HTTPError as e:
            body = e.read().decode(errors="replace")
            log.warning(f"Pluto TV [{lang}] boot HTTP {e.code}: {body[:500]}")
            return None
        except Exception as e:
            log.warning(f"Pluto TV [{lang}] boot failed: {e}")
            return None
        log.info(f"Pluto TV [{lang}] boot response keys: {list(data.keys())}")
        session_token = data.get("sessionToken", "")
        params = data.get("stitcherParams", "")
        refresh = int(data.get("refreshInSec", 28800))
        if not params:
            log.warning(f"Pluto TV [{lang}] boot returned no stitcherParams. Full response: {raw[:1000]}")
            return None
        return device_id, session_token, params, refresh

    def _fetch_lang(self, lang: str):
        import urllib.request
        boot = self._boot(lang)
        if boot is None:
            with self._lock:
                self._errors[lang] = "boot API failed"
            return
        device_id, session_token, stitcher_params, refresh_in = boot

        _, xff = self._lang_context(lang)
        api_url = (
            f"https://api.pluto.tv/v2/channels"
            f"?lang={lang}&deviceType=web&deviceId={device_id}"
            f"&appName=web&appVersion={PLUTO_APP_VERSION}&clientTime=0"
        )
        try:
            headers = {
                "User-Agent": _BROWSER_UA,
                "Referer": "https://pluto.tv/",
                "Origin": "https://pluto.tv",
            }
            if session_token:
                headers["Authorization"] = f"Bearer {session_token}"
            if xff:
                headers["X-Forwarded-For"] = xff
            req = urllib.request.Request(
                api_url, headers=headers
            )
            with urllib.request.urlopen(req, timeout=15) as resp:
                body = resp.read().decode()
                raw = json.loads(body)
        except urllib.error.HTTPError as e:
            body = e.read().decode(errors="replace")
            with self._lock:
                self._errors[lang] = f"HTTP {e.code}"
            log.warning(f"Pluto TV [{lang}] channels HTTP {e.code}: {body[:500]}")
            return
        except Exception as e:
            with self._lock:
                self._errors[lang] = str(e)
            log.warning(f"Pluto TV [{lang}] channels fetch failed: {e}")
            return
        log.info(f"Pluto TV [{lang}] channels response: {len(raw) if isinstance(raw, list) else type(raw).__name__}")

        channels = []
        for ch in raw:
            if not ch.get("isStitched"):
                continue
            urls = ch.get("stitched", {}).get("urls", [])
            hls_url = next(
                (u.get("url", "") for u in urls if u.get("type") == "hls"),
                None,
            )
            if not hls_url:
                continue
            # Keep the original URL template and inject fresh stitcher params.
            stitched_url = self._apply_stitcher_params(hls_url, stitcher_params, session_token)
            channels.append({
                "id":       ch.get("_id", ""),
                "name":     ch.get("name", ""),
                "category": ch.get("category", ""),
                "hls_url":  hls_url,
                "url":      stitched_url,
            })
        channels.sort(key=lambda c: (c["category"], c["name"]))

        with self._lock:
            self._by_lang[lang] = channels
            self._errors.pop(lang, None)
            self._sessions[lang] = (device_id, session_token, stitcher_params,
                                    time.time() + refresh_in)
        meta = self.get_meta(lang)
        log.info(
            f"Pluto TV [{lang}] region={meta.get('region')} country={meta.get('country')} "
            f"xff={meta.get('xff') or '-'}: loaded {len(channels)} channels "
            f"(refresh in {refresh_in//3600}h)"
        )

    def refresh_all(self):
        for lang in PLUTO_LANGS:
            self._fetch_lang(lang)

    def start_background_refresh(self):
        def _loop():
            while True:
                now = time.time()
                for lang in PLUTO_LANGS:
                    with self._lock:
                        _, _, _, refresh_at = self._sessions.get(lang, ("", "", "", 0))
                    if now >= refresh_at:
                        self._fetch_lang(lang)
                time.sleep(300)  # check every 5 min
        threading.Thread(target=_loop, daemon=True).start()


pluto_cache = PlutoCache()


# ── Pipeline ──────────────────────────────────────────────────────────────────
def _probe_fps(url: str) -> float | None:
    """Ask ffprobe for the video stream's frame rate. Returns None on failure."""
    try:
        r = subprocess.run(
            [
                "ffprobe", "-v", "quiet",
                "-select_streams", "v:0",
                "-show_entries", "stream=r_frame_rate",
                "-of", "default=noprint_wrappers=1:nokey=1",
                url,
            ],
            capture_output=True, text=True, timeout=10,
        )
        val = r.stdout.strip().splitlines()[0] if r.returncode == 0 else ""
        if not val:
            return None
        if "/" in val:
            num, den = val.split("/", 1)
            den = float(den)
            return round(float(num) / den, 3) if den else None
        return float(val)
    except Exception:
        return None


def _yt_lang_args() -> list[str]:
    """Extra yt-dlp flags to request content in the configured YT_LANG."""
    if not YT_LANG:
        return []
    # Pass lang to both extractors: youtubetab (channel/playlist pages) and
    # youtube (individual video pages / search). This sets hl= in InnerTube
    # requests so YouTube returns translated titles when available.
    return [
        "--extractor-args", f"youtube:lang={YT_LANG}",
        "--extractor-args", f"youtubetab:lang={YT_LANG}",
        "--add-header", f"Accept-Language:{YT_LANG}-{YT_LANG.upper()},{YT_LANG};q=0.9,*;q=0.5",
    ]


def fetch_title(stream: Stream):
    if _is_direct_stream(stream.url):
        return  # no yt-dlp for direct streams; title stays empty
    try:
        r = subprocess.run(
            ["yt-dlp", "--js-runtimes", "node", "--no-playlist", "--print", "title", stream.url],
            capture_output=True, text=True, timeout=15
        )
        if r.returncode == 0:
            with stream.lock:
                stream.title = r.stdout.strip()
    except Exception:
        pass


def _fetch_duration_s(url: str) -> int:
    """Return video duration in seconds via yt-dlp, or 0 if live/unknown."""
    if _is_direct_stream(url):
        return 0
    try:
        r = subprocess.run(
            ["yt-dlp", "--js-runtimes", "node", "--no-playlist",
             "--print", "%(duration)s\t%(is_live)s", "--quiet", url],
            capture_output=True, text=True, timeout=20,
        )
        if r.returncode != 0:
            return 0
        parts = r.stdout.strip().split("\t")
        is_live = (parts[1].strip().lower() if len(parts) > 1 else "") in ("true", "1")
        if is_live:
            return 0
        try:
            return max(0, int(float(parts[0].strip())))
        except (ValueError, IndexError):
            return 0
    except Exception:
        return 0


def _is_direct_hls(url: str) -> bool:
    """True for raw HLS manifest URLs that ffmpeg can consume directly."""
    from urllib.parse import urlparse
    path = urlparse(url).path.lower()
    return path.endswith(".m3u8") or path.endswith(".m3u")


def _is_local_media_url(url: str) -> bool:
    """True for local file URLs served by the Local Media tab."""
    return url.startswith("file://")


def _is_acestream(url: str) -> bool:
    """True for acestream-http-proxy URLs (MPEG-TS over HTTP)."""
    return "/ace/getstream" in url or "/ace/manifest.m3u8" in url


def _is_pluto_stream(url: str) -> bool:
    """True for Pluto TV stitched stream URLs."""
    from urllib.parse import urlparse
    return "pluto.tv" in (urlparse(url).netloc or "").lower()


def _is_rtp_stream(url: str) -> bool:
    """True for RTP/UDP multicast streams that ffmpeg can consume directly."""
    return url.startswith(("rtp://", "udp://", "rtsp://", "srt://"))


_PRIVATE_IP_RE = re.compile(
    r"^https?://"
    r"(?:127\.\d+\.\d+\.\d+|"
    r"10\.\d+\.\d+\.\d+|"
    r"172\.(?:1[6-9]|2\d|3[01])\.\d+\.\d+|"
    r"192\.168\.\d+\.\d+|"
    r"localhost)"
    r"(?::\d+)?/"
)

def _is_local_network_stream(url: str) -> bool:
    """True for HTTP streams served from private/local IPs (e.g. IPTV middleware)."""
    return bool(_PRIVATE_IP_RE.match(url))


def _is_direct_stream(url: str) -> bool:
    """True for any URL ffmpeg can consume directly without yt-dlp."""
    return (_is_direct_hls(url) or _is_acestream(url) or _is_local_media_url(url)
            or _is_rtp_stream(url) or _is_local_network_stream(url))


def _is_youtube_url(url: str) -> bool:
    """True for YouTube watch/channel URLs."""
    return "youtube.com" in url or "youtu.be" in url


def _is_twitch_url(url: str) -> bool:
    """True for Twitch stream URLs."""
    return "twitch.tv" in url


def _default_sync_ms_for_url(url: str) -> int:
    """Return the default sync delay (ms) based on stream source type."""
    if _is_youtube_url(url) or _is_twitch_url(url):
        return 500
    if _is_pluto_stream(url):
        return 500
    if _is_direct_hls(url) or _is_local_network_stream(url):
        # IPTV / HLS streams
        return 1000
    return AUDIO_DELAY_MS


def _ffmpeg_input_target(url: str) -> str:
    """Return ffmpeg-safe input target from stream url."""
    if _is_local_media_url(url):
        parsed = urlparse(url)
        return unquote(parsed.path or "")
    return url


def _has_supported_media_ext(path: str) -> bool:
    """True when path or its symlink target has an allowed video extension."""
    ext = os.path.splitext(path)[1].lower()
    if ext in LOCAL_MEDIA_EXTS:
        return True
    if os.path.islink(path):
        target_ext = os.path.splitext(os.path.realpath(path))[1].lower()
        return target_ext in LOCAL_MEDIA_EXTS
    return False


def _has_supported_iptv_list_ext(path: str) -> bool:
    ext = os.path.splitext(path)[1].lower()
    return ext in IPTV_LIST_EXTS


def _parse_extinf_name(line: str) -> str:
    # #EXTINF:-1 ... ,Channel Name
    # Prefer the explicit title after the first comma.
    _, _, tail = line.partition(",")
    title = (tail or "").strip()
    if title:
        return title

    # Fallback to tvg-name metadata if present.
    marker = 'tvg-name="'
    pos = line.find(marker)
    if pos != -1:
        rest = line[pos + len(marker):]
        value, _, _ = rest.partition('"')
        return value.strip()
    return ""


def _parse_iptv_m3u(content: str) -> list[dict[str, str]]:
    streams: list[dict[str, str]] = []
    pending_name = ""

    for raw_line in content.splitlines():
        line = raw_line.strip()
        if not line:
            continue
        if line.startswith("#EXTINF"):
            pending_name = _parse_extinf_name(line)
            continue
        if line.startswith("#"):
            continue

        url = line
        name = pending_name or f"Stream {len(streams) + 1}"
        streams.append({"name": name, "url": url})
        pending_name = ""

    return streams


_ace_streams_lock = threading.Lock()

def _load_ace_streams() -> list[dict]:
    if not os.path.isfile(ACE_STREAMS_FILE):
        return []
    try:
        with open(ACE_STREAMS_FILE, encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return []

def _save_ace_streams(streams: list[dict]) -> None:
    os.makedirs(os.path.dirname(ACE_STREAMS_FILE) or ".", exist_ok=True)
    with _ace_streams_lock:
        with open(ACE_STREAMS_FILE, "w", encoding="utf-8") as f:
            json.dump(streams, f, indent=2)


_favorites_lock = threading.Lock()

def _load_favorites() -> list[str]:
    """Return list of favorited channel URLs."""
    if not os.path.isfile(FAVORITES_FILE):
        return []
    try:
        with open(FAVORITES_FILE, encoding="utf-8") as f:
            data = json.load(f)
            return data if isinstance(data, list) else []
    except Exception:
        return []

def _save_favorites(urls: list[str]) -> None:
    os.makedirs(os.path.dirname(FAVORITES_FILE) or ".", exist_ok=True)
    with _favorites_lock:
        with open(FAVORITES_FILE, "w", encoding="utf-8") as f:
            json.dump(urls, f, indent=2)


_progress_lock = threading.Lock()

def _load_progress() -> dict:
    """Return {url: {pos_s, saved_at}} dict."""
    if not os.path.isfile(PROGRESS_FILE):
        return {}
    try:
        with open(PROGRESS_FILE, encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return {}

def _save_progress(data: dict) -> None:
    os.makedirs(os.path.dirname(PROGRESS_FILE) or ".", exist_ok=True)
    with _progress_lock:
        with open(PROGRESS_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)


# ── Home feed cache ───────────────────────────────────────────────────────────
_home_feed_cache: dict = {"videos": [], "built_at": 0.0}
_home_feed_lock  = threading.Lock()


def _load_home_feed_disk_cache() -> None:
    """Load persisted home feed cache from disk on startup."""
    try:
        if os.path.isfile(HOME_FEED_CACHE_FILE):
            with open(HOME_FEED_CACHE_FILE, encoding="utf-8") as f:
                data = json.load(f)
            videos = data.get("videos") or []
            if videos and data.get("built_at"):
                ts_dated = [v for v in videos if v.get("published_ts")]
                ts_dated.sort(key=lambda v: v["published_ts"], reverse=True)
                remaining = [v for v in videos if not v.get("published_ts")]
                dated   = [v for v in remaining if v.get("upload_date")]
                undated = [v for v in remaining if not v.get("upload_date")]
                dated.sort(key=lambda v: v["upload_date"], reverse=True)
                undated.sort(key=lambda v: v.get("fetch_idx", 0))
                videos = ts_dated + dated + undated
                _home_feed_cache["videos"]   = videos
                _home_feed_cache["built_at"] = float(data["built_at"])
                log.info(f"Loaded home feed cache from disk: {len(videos)} videos ({len(dated)} dated)")
    except Exception as e:
        log.warning(f"Could not load home feed disk cache: {e}")


def _save_home_feed_disk_cache(videos: list[dict], built_at: float) -> None:
    """Persist home feed cache to disk so it survives container restarts."""
    try:
        os.makedirs(os.path.dirname(HOME_FEED_CACHE_FILE), exist_ok=True)
        tmp = HOME_FEED_CACHE_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump({"videos": videos, "built_at": built_at}, f)
        os.replace(tmp, HOME_FEED_CACHE_FILE)
    except Exception as e:
        log.warning(f"Could not save home feed disk cache: {e}")


_CHANNEL_ID_CACHE: dict[str, str] = {}
_CHANNEL_ID_LOCK = threading.Lock()
_UC_RE = re.compile(r"UC[A-Za-z0-9_-]{22}")
_YT_UA = "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0 Safari/537.36"


def _resolve_channel_id(channel_url: str) -> str:
    """Return the UC... channel ID for a YouTube channel URL, or '' on failure. Cached."""
    if not channel_url:
        return ""
    with _CHANNEL_ID_LOCK:
        if channel_url in _CHANNEL_ID_CACHE:
            return _CHANNEL_ID_CACHE[channel_url]
    m = re.search(r"/channel/(UC[A-Za-z0-9_-]{22})", channel_url)
    cid = m.group(1) if m else ""
    if not cid:
        try:
            req = Request(channel_url, headers={"User-Agent": _YT_UA, "Accept-Language": "en-US,en;q=0.9"})
            with urlopen(req, timeout=15) as resp:
                html = resp.read(400_000).decode("utf-8", errors="replace")
            m = _UC_RE.search(html)
            cid = m.group(0) if m else ""
        except Exception:
            cid = ""
    with _CHANNEL_ID_LOCK:
        _CHANNEL_ID_CACHE[channel_url] = cid
    return cid


def _fetch_rss_published(channel_id: str) -> dict[str, str]:
    """Return {video_id: ISO-8601 published} for a channel via YouTube's Atom feed."""
    if not channel_id:
        return {}
    url = f"https://www.youtube.com/feeds/videos.xml?channel_id={channel_id}"
    try:
        req = Request(url, headers={"User-Agent": _YT_UA})
        with urlopen(req, timeout=15) as resp:
            xml = resp.read().decode("utf-8", errors="replace")
    except Exception:
        return {}
    out: dict[str, str] = {}
    # Atom entries are small enough to parse with a regex pair.
    for entry in re.findall(r"<entry>(.*?)</entry>", xml, flags=re.DOTALL):
        vid_m = re.search(r"<yt:videoId>([^<]+)</yt:videoId>", entry)
        pub_m = re.search(r"<published>([^<]+)</published>", entry)
        if vid_m and pub_m:
            out[vid_m.group(1).strip()] = pub_m.group(1).strip()
    return out


def _fetch_channel_videos(channel_url: str, channel_name: str, n: int) -> list[dict]:
    """Fetch the n most recent videos for one channel. Returns [] on any failure."""
    try:
        r = subprocess.run(
            [
                "yt-dlp",
                "--js-runtimes", "node",
                "--flat-playlist",
                "--playlist-end", str(n),
                "--print", "%(id)s\t%(title)s\t%(duration)s\t%(thumbnail)s\t%(webpage_url)s\t%(upload_date)s",
                "--no-warnings",
                "--quiet",
                *_yt_lang_args(),
                channel_url,
            ],
            capture_output=True, text=True, timeout=25,
        )
    except Exception:
        return []

    if r.returncode != 0:
        return []

    videos = []
    for line in r.stdout.strip().splitlines():
        parts = line.split("\t", 5)
        if len(parts) < 2:
            continue
        vid_id      = parts[0].strip()
        title       = parts[1].strip()
        duration    = parts[2].strip() if len(parts) > 2 else ""
        thumb       = parts[3].strip() if len(parts) > 3 else ""
        webpage     = parts[4].strip() if len(parts) > 4 else ""
        upload_date = parts[5].strip() if len(parts) > 5 else ""
        if not vid_id or vid_id == "NA":
            continue
        # Skip Shorts: duration <= 60s, or webpage URL is a /shorts/ link.
        try:
            if duration and duration != "NA" and float(duration) <= 60:
                continue
        except ValueError:
            pass
        if webpage and "/shorts/" in webpage:
            continue
        video_url = webpage if (webpage and webpage != "NA") else f"https://www.youtube.com/watch?v={vid_id}"
        if not thumb or thumb == "NA":
            thumb = f"https://i.ytimg.com/vi/{vid_id}/mqdefault.jpg"
        videos.append({
            "id":          vid_id,
            "title":       title,
            "duration":    duration,
            "thumb":       thumb,
            "url":         video_url,
            "upload_date": upload_date if upload_date and upload_date != "NA" else "",
            "channel":     channel_name,
            "channel_url": channel_url,
            "fetch_idx":   len(videos),  # position within channel (0 = newest)
        })

    # Enrich with precise publish timestamps from the channel's Atom feed.
    # This is how we get a reliable cross-channel sort order for the Home feed,
    # since --flat-playlist almost never returns upload_date for YouTube tabs.
    if videos:
        cid = _resolve_channel_id(channel_url)
        rss = _fetch_rss_published(cid) if cid else {}
        if rss:
            for v in videos:
                ts = rss.get(v["id"])
                if ts:
                    v["published_ts"] = ts            # ISO-8601, sortable as string
                    if not v.get("upload_date"):
                        v["upload_date"] = ts[:10].replace("-", "")  # YYYYMMDD
    return videos


def _build_home_feed(channels: list[dict]) -> list[dict]:
    """Fetch recent videos from all channels concurrently and return sorted list."""
    all_videos: list[dict] = []
    with ThreadPoolExecutor(max_workers=HOME_FEED_WORKERS) as pool:
        futures = {
            pool.submit(_fetch_channel_videos, ch["url"], ch["name"], HOME_FEED_PER_CHANNEL): ch
            for ch in channels
        }
        for future in as_completed(futures):
            try:
                all_videos.extend(future.result())
            except Exception:
                pass

    # Prefer precise RSS publish timestamps when available so videos from
    # different channels interleave by true recency, like YouTube's home feed.
    ts_dated = [v for v in all_videos if v.get("published_ts")]
    ts_dated.sort(key=lambda v: v["published_ts"], reverse=True)
    remaining = [v for v in all_videos if not v.get("published_ts")]
    dated   = [v for v in remaining if v.get("upload_date")]
    undated = [v for v in remaining if not v.get("upload_date")]
    dated.sort(key=lambda v: v["upload_date"], reverse=True)  # newest first

    # True round-robin interleave for undated videos: group by channel_url,
    # sort each group by fetch_idx (0=newest), then zip across channels so
    # position 0 is newest from every channel before showing position 1, etc.
    by_channel: dict[str, list] = {}
    for v in undated:
        key = v.get("channel_url") or v.get("channel") or ""
        by_channel.setdefault(key, []).append(v)
    for lst in by_channel.values():
        lst.sort(key=lambda v: v.get("fetch_idx", 0))
    interleaved: list[dict] = []
    channels_lists = list(by_channel.values())
    max_len = max((len(l) for l in channels_lists), default=0)
    for i in range(max_len):
        for lst in channels_lists:
            if i < len(lst):
                interleaved.append(lst[i])

    return ts_dated + dated + interleaved


def _scan_iptv_lists() -> tuple[str, list[dict[str, str]], str]:
    base = os.path.abspath(IPTV_LISTS_DIR)
    if not os.path.isdir(base):
        return base, [], f"IPTV lists directory not found: {base}"

    lists: list[dict[str, str]] = []
    try:
        for root, _, names in os.walk(base, followlinks=True):
            for filename in names:
                full = os.path.join(root, filename)
                if not os.path.isfile(full):
                    continue
                if not _has_supported_iptv_list_ext(full):
                    continue
                rel = os.path.relpath(full, base).replace(os.sep, "/")
                name = os.path.splitext(os.path.basename(rel))[0]
                lists.append({"id": rel, "name": name, "path": rel})
    except Exception as e:
        return base, [], f"Failed to scan IPTV lists folder: {e}"

    lists.sort(key=lambda x: x["path"].lower())
    return base, lists, ""


_BROWSER_UA = (
    "Mozilla/5.0 (X11; Linux x86_64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/120.0.0.0 Safari/537.36"
)


def _probe_local_codecs(abs_path: str) -> tuple[str, str]:
    """Return (video_codec, audio_codec) for a local file using ffprobe. Empty string if not found."""
    try:
        r = subprocess.run(
            [
                "ffprobe", "-v", "error",
                "-select_streams", "v:0", "-show_entries", "stream=codec_name",
                "-of", "default=noprint_wrappers=1:nokey=1",
                abs_path,
            ],
            capture_output=True, text=True, timeout=5,
        )
        vcodec = r.stdout.strip().lower()
        r2 = subprocess.run(
            [
                "ffprobe", "-v", "error",
                "-select_streams", "a:0", "-show_entries", "stream=codec_name",
                "-of", "default=noprint_wrappers=1:nokey=1",
                abs_path,
            ],
            capture_output=True, text=True, timeout=5,
        )
        acodec = r2.stdout.strip().lower()
        return vcodec, acodec
    except Exception:
        return "", ""


def _direct_input_args(url: str) -> list[str]:
    """ffmpeg input flags for a direct stream URL."""
    from urllib.parse import urlparse, parse_qs
    if _is_local_media_url(url):
        return ["-re"]
    if _is_acestream(url):
        return ["-timeout", "10000000"]
    if _is_rtp_stream(url):
        return ["-rtbufsize", "100M"]
    parsed = urlparse(url)
    host = parsed.netloc.lower()
    headers = ""
    if "pluto.tv" in host:
        country = (parse_qs(parsed.query).get("country", [""])[0] or "").upper()
        xff = ""
        if country:
            for lang_code, region_code in PLUTO_REGION_MAP.items():
                if region_code.upper() == country:
                    xff = PLUTO_XFF_MAP.get(lang_code, "")
                    if xff:
                        break
        headers = (
            "Referer: https://pluto.tv/\r\n"
            "Origin: https://pluto.tv\r\n"
            "Accept-Language: en-US,en;q=0.9\r\n"
        )
        if xff:
            headers += f"X-Forwarded-For: {xff}\r\n"
    args = ["-user_agent", _BROWSER_UA]
    if headers:
        args += ["-headers", headers]
    # Don't use -re for Pluto live HLS: let ffmpeg buffer ahead for smoother output.
    if "pluto.tv" not in host:
        args.append("-re")
    return args


def _resolve_mp4_url(url: str, quality: int | None) -> tuple[str, str]:
    """Resolve a direct playable URL for MP4/native mode. Returns (direct_url, error)."""
    # Local files: transcode via /stream_fmp4 to ensure H.264+AAC browser compat
    # (handles Xvid, AC3, DTS, MPEG-2, HEVC and any other unsupported codec)
    if _is_local_media_url(url):
        return "/stream_fmp4?url=" + quote(url, safe=""), ""

    # Pluto TV live HLS: Chrome/Firefox can't play HLS natively, transcode via /stream_fmp4
    if _is_pluto_stream(url) or _is_direct_hls(url):
        return "/stream_fmp4?url=" + quote(url, safe=""), ""

    # Acestream, RTP/UDP/RTSP, LAN MPEG-TS — browser can't play these natively;
    # transcode to fragmented MP4 on the fly via /stream_fmp4
    if _is_acestream(url) or _is_rtp_stream(url) or _is_local_network_stream(url):
        return "/stream_fmp4?url=" + quote(url, safe=""), ""

    # YouTube, Twitch, etc: resolve a direct CDN URL via yt-dlp and serve it
    # directly to the browser. Prefer H.264+AAC so no transcoding is needed.
    fmt = (
        f"best[vcodec^=avc][height<={quality}]/best[vcodec^=avc]/best[height<={quality}]/best"
        if quality
        else "best[vcodec^=avc]/best"
    )
    try:
        r = subprocess.run(
            ["yt-dlp", "--js-runtimes", "node", "--no-playlist",
             "-f", fmt, "--get-url", "--quiet", url],
            capture_output=True, text=True, timeout=30,
        )
        if r.returncode == 0:
            lines = [l.strip() for l in r.stdout.strip().splitlines() if l.strip()]
            if lines:
                return lines[0], ""
    except Exception as e:
        return "", str(e)
    return "", "Could not resolve a direct playable URL"


def _start_audio_buffer(stream: Stream):
    """Spawn a dedicated ffmpeg process to fill stream._audio_chunks with MP3.
    Used by the normal MJPEG pipeline for direct HLS streams."""
    extra = []
    if _is_acestream(stream.url) or _is_local_network_stream(stream.url):
        extra = ["-probesize", "20M", "-analyzeduration", "10M"]
    seek_args = ["-ss", str(int(stream.seek_s))] if stream.seek_s > 0 else []
    audio_cmd = [
        "ffmpeg",
        "-loglevel", "error",
        *_direct_input_args(stream.url),
        *seek_args,
        *extra,
        "-i", _ffmpeg_input_target(stream.url),
        "-vn",
        "-af", "aresample=async=1:first_pts=0",
        "-c:a", "mp3",
        "-b:a", "128k",
        "-f", "mp3",
        "pipe:1",
    ]
    audio_proc = subprocess.Popen(
        audio_cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL
    )
    with stream.lock:
        stream._audio_proc = audio_proc
    with stream._audio_lock:
        stream._audio_chunks.clear()
        stream._audio_done = False
    stream._audio_ready.clear()

    def _drain():
        try:
            while True:
                chunk = audio_proc.stdout.read(8192)
                if not chunk:
                    break
                with stream._audio_lock:
                    stream._audio_chunks.append(chunk)
                stream._audio_ready.set()
        finally:
            with stream._audio_lock:
                stream._audio_done = True
            stream._audio_ready.set()

    threading.Thread(target=_drain, daemon=True).start()


def _start_audio_buffer_any(stream: Stream):
    """Fill stream._audio_chunks with MP3 for any stream type (audio-only mode).
    For direct streams uses ffmpeg directly; for YouTube/Twitch uses yt-dlp first."""
    if _is_direct_stream(stream.url):
        _start_audio_buffer(stream)
        return

    # Non-direct (YouTube, Twitch, etc): resolve audio URL via yt-dlp first
    audio_fmt = "bestaudio[ext=m4a]/bestaudio"
    seek_args: list[str] = ["-ss", str(int(stream.seek_s))] if stream.seek_s > 0 else []
    try:
        url_r = subprocess.run(
            ["yt-dlp", "--js-runtimes", "node", "--no-playlist",
             "-f", audio_fmt, "--get-url", "--quiet", stream.url],
            capture_output=True, text=True, timeout=30,
        )
        direct_url = url_r.stdout.strip().splitlines()[0] if url_r.returncode == 0 else ""
    except Exception:
        direct_url = ""

    if direct_url:
        ff_cmd = [
            "ffmpeg", "-loglevel", "error",
            "-reconnect", "1", "-reconnect_streamed", "1", "-reconnect_delay_max", "10",
            *seek_args,
            "-re", "-i", direct_url,
            "-vn", "-af", "aresample=async=1:first_pts=0",
            "-c:a", "mp3", "-b:a", "128k", "-f", "mp3", "pipe:1",
        ]
        ff_proc = subprocess.Popen(ff_cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        yt_proc = None
    else:
        yt_cmd = [
            "yt-dlp", "--js-runtimes", "node", "--no-playlist",
            "-f", audio_fmt, "-o", "-", "--quiet", stream.url,
        ]
        ff_cmd = [
            "ffmpeg", "-loglevel", "error",
            "-i", "pipe:0", "-vn",
            "-af", "aresample=async=1:first_pts=0",
            "-c:a", "mp3", "-b:a", "128k", "-f", "mp3", "pipe:1",
        ]
        yt_proc = subprocess.Popen(yt_cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        ff_proc = subprocess.Popen(ff_cmd, stdin=yt_proc.stdout,
                                   stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)

    with stream.lock:
        stream._audio_proc = ff_proc
    with stream._audio_lock:
        stream._audio_chunks.clear()
        stream._audio_done = False
    stream._audio_ready.clear()

    def _drain():
        try:
            while True:
                chunk = ff_proc.stdout.read(8192)
                if not chunk:
                    break
                with stream._audio_lock:
                    stream._audio_chunks.append(chunk)
                stream._audio_ready.set()
        finally:
            with stream._audio_lock:
                stream._audio_done = True
            stream._audio_ready.set()
            for p in (ff_proc, yt_proc):
                if p and p.poll() is None:
                    try:
                        p.terminate()
                    except Exception:
                        pass

    threading.Thread(target=_drain, daemon=True).start()


def _start_muxed_pipeline(stream: Stream):
    """
    Start a single ffmpeg process for direct streams that outputs:
    - video MJPEG frames on stdout (pipe:1)
    - audio MP3 chunks on fd 3 (pipe:3)
    This avoids a second source connection for audio.
    """
    vf = (
        f"scale={STREAM_WIDTH}:{STREAM_HEIGHT}"
        f":force_original_aspect_ratio=decrease,"
        f"pad={STREAM_WIDTH}:{STREAM_HEIGHT}:(ow-iw)/2:(oh-ih)/2:black"
    )
    audio_r, audio_w = os.pipe()
    audio_out = [
        "-map", "0:a:0?",
        "-vn",
    ]
    # Local files are stable sources; skip async resampler to avoid periodic
    # audible artifacts on some ffmpeg + browser combinations.
    if not _is_local_media_url(stream.url):
        audio_out += ["-af", "aresample=async=1:first_pts=0"]
    audio_out += [
        "-c:a", "mp3",
        "-b:a", "128k",
        "-ar", "48000",
        "-ac", "2",
        "-f", "mp3",
        f"pipe:{audio_w}",
    ]

    seek_args = ["-ss", str(int(stream.seek_s))] if stream.seek_s > 0 else []
    ff_cmd = [
        "ffmpeg",
        "-loglevel", "error",
        *_direct_input_args(stream.url),
        *seek_args,
        "-probesize", "20M",
        "-analyzeduration", "10M",
        "-i", _ffmpeg_input_target(stream.url),
        # Video output (stdout / pipe:1)
        "-map", "0:v:0",
        "-vf", vf,
        "-vcodec", "mjpeg",
        "-q:v", str(FFMPEG_QUALITY),
        "-r", str(MJPEG_FPS),
        "-f", "image2pipe",
        "-vframes", "99999999",
        "pipe:1",
        # Audio output (extra fd / pipe:3)
        *audio_out,
    ]
    try:
        ff_proc = subprocess.Popen(
            ff_cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            pass_fds=(audio_w,),
        )
    except Exception:
        os.close(audio_r)
        raise
    finally:
        os.close(audio_w)

    with stream._audio_lock:
        stream._audio_chunks.clear()
        stream._audio_done = False
    stream._audio_ready.clear()

    def _drain():
        try:
            with os.fdopen(audio_r, "rb", buffering=0) as audio_pipe:
                while True:
                    chunk = audio_pipe.read(8192)
                    if not chunk:
                        break
                    with stream._audio_lock:
                        stream._audio_chunks.append(chunk)
                    stream._audio_ready.set()
        finally:
            with stream._audio_lock:
                stream._audio_done = True
            stream._audio_ready.set()

    threading.Thread(target=_drain, daemon=True).start()
    return ff_proc


def _run_hls_pipeline(stream: Stream):
    """Pipeline for direct streams (HLS / MPEG-TS / Acestream) — no yt-dlp."""
    is_ace = _is_acestream(stream.url)
    is_pluto = _is_pluto_stream(stream.url)
    is_local = _is_local_media_url(stream.url)
    is_rtp = _is_rtp_stream(stream.url)
    is_lan = _is_local_network_stream(stream.url)
    log.info(
        f"[{stream.id}] Direct pipeline (ace={is_ace}, pluto={is_pluto}, local={is_local}, rtp={is_rtp}, lan={is_lan}, audio_only={stream.audio_only})"
    )

    if stream.audio_only:
        try:
            _start_audio_buffer(stream)
            with stream.lock:
                stream.status = "streaming"
                if stream.started_at is None:
                    stream.started_at = time.time()
            # Wait for audio to finish
            stream._audio_ready.wait()
            while True:
                stream._audio_ready.clear()
                with stream._audio_lock:
                    if stream._audio_done:
                        break
                stream._audio_ready.wait()
            with stream.lock:
                stream.status = "done"
        except Exception as e:
            with stream.lock:
                stream.status = "error"
                stream.error = str(e)
            log.error(f"[{stream.id}] Audio-only pipeline error: {e}")
        finally:
            stream.stop()
        return

    SOI = b"\xff\xd8"
    EOI = b"\xff\xd9"
    try:
        if is_ace or is_pluto or is_local or is_rtp or is_lan:
            ff_proc = _start_muxed_pipeline(stream)
        else:
            # HLS path still uses a dedicated audio process.
            _start_audio_buffer(stream)
            ff_cmd = [
                "ffmpeg",
                "-loglevel", "error",
                *_direct_input_args(stream.url),
                "-i", _ffmpeg_input_target(stream.url),
                "-vf", (
                    f"scale={STREAM_WIDTH}:{STREAM_HEIGHT}"
                    f":force_original_aspect_ratio=decrease,"
                    f"pad={STREAM_WIDTH}:{STREAM_HEIGHT}:(ow-iw)/2:(oh-ih)/2:black"
                ),
                "-vcodec", "mjpeg",
                "-q:v", str(FFMPEG_QUALITY),
                "-r", str(MJPEG_FPS),
                "-an",
                "-f", "image2pipe",
                "-vframes", "99999999",
                "pipe:1",
            ]
            ff_proc = subprocess.Popen(
                ff_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE
            )
        with stream.lock:
            stream._ff_proc = ff_proc
            stream.status = "streaming"
            if stream.started_at is None:
                stream.started_at = time.time()

        buf = b""
        while True:
            chunk = ff_proc.stdout.read(65536)
            if not chunk:
                break
            buf += chunk
            while True:
                start = buf.find(SOI)
                if start == -1:
                    buf = b""
                    break
                end = buf.find(EOI, start + 2)
                if end == -1:
                    buf = buf[start:]
                    break
                frame = buf[start:end + 2]
                buf = buf[end + 2:]
                with stream.frame_cond:
                    stream.frame = frame
                    stream._frame_history.append((time.time(), frame))
                    stream.last_used = time.time()
                    if stream.first_frame_at is None:
                        stream.first_frame_at = time.time()
                    stream.frame_cond.notify_all()

        ff_rc = ff_proc.poll()
        produced = stream.frame is not None
        with stream.lock:
            if produced:
                stream.status = "done"
            else:
                ff_err = ff_proc.stderr.read(500).decode("utf-8", errors="replace")
                stream.status = "error"
                stream.error = "No video frames from HLS stream"
                stream.error_detail = f"ff_rc={ff_rc} ff_err={ff_err}"
        log.info(f"[{stream.id}] HLS pipeline finished (rc={ff_rc})")
    except Exception as e:
        with stream.lock:
            stream.status = "error"
            stream.error = str(e)
        log.error(f"[{stream.id}] HLS pipeline error: {e}")
    finally:
        stream.stop()


def run_pipeline(stream: Stream):
    log.info(f"[{stream.id}] Starting pipeline for: {stream.url}")
    threading.Thread(target=fetch_title, args=(stream,), daemon=True).start()

    if _is_direct_stream(stream.url):
        _run_hls_pipeline(stream)
        return

    if stream.audio_only:
        # Start unified audio buffer (works for all stream types) then return —
        # no MJPEG pipeline is needed. _serve_audio drains from _audio_chunks.
        threading.Thread(target=_start_audio_buffer_any, args=(stream,), daemon=True).start()
        with stream.lock:
            stream.status = "streaming"
            if stream.started_at is None:
                stream.started_at = time.time()
        return

    try:
        def _format_candidates(quality: int | None) -> list[str]:
            if quality:
                q = quality
                return [
                    f"bestvideo[ext=mp4][height<={q}]/best[ext=mp4][height<={q}]",
                    f"bestvideo[height<={q}]/best[height<={q}]",
                    "bestvideo[ext=mp4]/best[ext=mp4]",
                    "bestvideo/best",
                ]
            return [
                "bestvideo[vcodec^=avc1][height<=720][fps<=30]/bestvideo[vcodec^=avc1][height<=720]/best[vcodec^=avc1][height<=720]/bestvideo[ext=mp4][height<=720]",
                "bestvideo/best",
            ]

        def _drain_stderr(pipe, sink: list[str], max_chars: int = 4000):
            try:
                while True:
                    chunk = pipe.read(1024)
                    if not chunk:
                        break
                    text = chunk.decode("utf-8", errors="replace")
                    sink.append(text)
                    current = sum(len(x) for x in sink)
                    if current > max_chars:
                        overflow = current - max_chars
                        while overflow > 0 and sink:
                            if len(sink[0]) <= overflow:
                                overflow -= len(sink[0])
                                sink.pop(0)
                            else:
                                sink[0] = sink[0][overflow:]
                                overflow = 0
            except Exception:
                pass

        SOI = b"\xff\xd8"
        EOI = b"\xff\xd9"
        attempt_errors: list[str] = []

        for attempt_idx, fmt in enumerate(_format_candidates(stream.quality), start=1):
            yt_proc = None

            # Always resolve a direct CDN URL first. This lets ffmpeg download
            # at real-time speed (-re) instead of letting yt-dlp race ahead and
            # buffer gigabytes into a pipe — which breaks long videos.
            url_r = subprocess.run(
                ["yt-dlp", "--js-runtimes", "node", "--no-playlist",
                 "-f", fmt, "--get-url", "--quiet", stream.url],
                capture_output=True, text=True, timeout=30,
            )
            direct_url = url_r.stdout.strip().splitlines()[0] if url_r.returncode == 0 else ""

            if direct_url:
                # Detect source FPS so we output at the native rate — no frame
                # duplication/dropping, which is the main cause of A/V drift.
                source_fps = _probe_fps(direct_url)
                output_fps = min(source_fps, MJPEG_FPS) if source_fps else MJPEG_FPS
                stream.fps = output_fps
                log.info(f"[{stream.id}] source_fps={source_fps} → output_fps={output_fps}")

                seek_args = ["-ss", str(int(stream.seek_s))] if stream.seek_s > 0 else []
                ff_cmd = [
                    "ffmpeg",
                    "-loglevel", "error",
                    "-reconnect", "1",
                    "-reconnect_streamed", "1",
                    "-reconnect_delay_max", "10",
                    *seek_args,
                    "-re",
                    "-i", direct_url,
                    "-vf", (
                        f"scale={STREAM_WIDTH}:{STREAM_HEIGHT}"
                        f":force_original_aspect_ratio=decrease,"
                        f"pad={STREAM_WIDTH}:{STREAM_HEIGHT}:(ow-iw)/2:(oh-ih)/2:black"
                    ),
                    "-vcodec", "mjpeg",
                    "-q:v", str(FFMPEG_QUALITY),
                    "-r", str(output_fps),
                    "-f", "image2pipe",
                    "-vframes", "99999999",
                    "pipe:1",
                ]
                ff_proc = subprocess.Popen(ff_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            else:
                # Fallback: pipe yt-dlp → ffmpeg (no seek support, may buffer on long videos)
                if stream.seek_s > 0:
                    attempt_errors.append(
                        f"attempt={attempt_idx} fmt={fmt} yt-dlp --get-url failed (seek requires direct URL): {url_r.stderr.strip()}"
                    )
                    continue
                log.warning(f"[{stream.id}] --get-url failed for fmt={fmt}, falling back to pipe")
                yt_cmd = [
                    "yt-dlp",
                    "--js-runtimes", "node",
                    "--no-playlist",
                    "-f", fmt,
                    "-o", "-",
                    "--quiet",
                    stream.url,
                ]
                ff_cmd = [
                    "ffmpeg",
                    "-loglevel", "error",
                    "-re",
                    "-i", "pipe:0",
                    "-vf", (
                        f"scale={STREAM_WIDTH}:{STREAM_HEIGHT}"
                        f":force_original_aspect_ratio=decrease,"
                        f"pad={STREAM_WIDTH}:{STREAM_HEIGHT}:(ow-iw)/2:(oh-ih)/2:black"
                    ),
                    "-vcodec", "mjpeg",
                    "-q:v", str(FFMPEG_QUALITY),
                    "-r", str(MJPEG_FPS),
                    "-f", "image2pipe",
                    "-vframes", "99999999",
                    "pipe:1",
                ]
                yt_proc = subprocess.Popen(yt_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                ff_proc = subprocess.Popen(ff_cmd, stdin=yt_proc.stdout,
                                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)

            yt_stderr_chunks: list[str] = []
            ff_stderr_chunks: list[str] = []

            with stream.lock:
                stream._yt_proc = yt_proc
                stream._ff_proc = ff_proc
                stream.status = "streaming"
                if stream.started_at is None:
                    stream.started_at = time.time()

            if yt_proc is not None:
                yt_err_t = threading.Thread(
                    target=_drain_stderr,
                    args=(yt_proc.stderr, yt_stderr_chunks),
                    daemon=True,
                )
                yt_err_t.start()
            ff_err_t = threading.Thread(
                target=_drain_stderr,
                args=(ff_proc.stderr, ff_stderr_chunks),
                daemon=True,
            )
            ff_err_t.start()

            log.info(f"[{stream.id}] Pipeline running (attempt {attempt_idx}, fmt={fmt})")

            frame_before = stream.frame
            buf = b""
            while True:
                chunk = ff_proc.stdout.read(65536)
                if not chunk:
                    break
                buf += chunk

                while True:
                    start = buf.find(SOI)
                    if start == -1:
                        buf = b""
                        break
                    end = buf.find(EOI, start + 2)
                    if end == -1:
                        buf = buf[start:]
                        break
                    frame = buf[start:end + 2]
                    buf = buf[end + 2:]
                    with stream.frame_cond:
                        stream.frame = frame
                        stream._frame_history.append((time.time(), frame))
                        stream.last_used = time.time()
                        if stream.first_frame_at is None:
                            stream.first_frame_at = time.time()
                        stream.frame_cond.notify_all()

            yt_rc = yt_proc.poll() if yt_proc is not None else None
            ff_rc = ff_proc.poll()
            yt_err = "".join(yt_stderr_chunks).strip()
            ff_err = "".join(ff_stderr_chunks).strip()
            if yt_proc is not None:
                yt_err_t.join(timeout=0.2)
            ff_err_t.join(timeout=0.2)

            produced_frames = stream.frame is not None and stream.frame is not frame_before
            if produced_frames:
                with stream.lock:
                    stream.status = "done"
                log.info(f"[{stream.id}] Pipeline finished")
                break

            attempt_errors.append(
                f"attempt={attempt_idx} fmt={fmt} yt_rc={yt_rc} ff_rc={ff_rc} "
                f"yt_err={yt_err[-220:]} ff_err={ff_err[-220:]}"
            )
            for proc in (ff_proc, yt_proc):
                if proc and proc.poll() is None:
                    try:
                        proc.terminate()
                    except Exception:
                        pass
        else:
            with stream.lock:
                stream.status = "error"
                stream.error = "No video frames were produced"
                stream.error_detail = " || ".join(attempt_errors)[-1800:]
            log.error(f"[{stream.id}] Pipeline failed: {stream.error_detail}")

    except Exception as e:
        with stream.lock:
            stream.status = "error"
            stream.error  = str(e)
            stream.error_detail = ""
        log.error(f"[{stream.id}] Pipeline error: {e}")
    finally:
        stream.stop()


# ── HTML ──────────────────────────────────────────────────────────────────────
STATUS_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>OpenCarStream — Streaming for Tesla vehicles</title>
<style>
  @import url('https://fonts.googleapis.com/css2?family=Orbitron:wght@700;900&family=Rajdhani:wght@300;500&display=swap');
  :root{--red:#e31937;--dark:#090909;--panel:#111117;--border:#252530;--text:#e0e0ee;--muted:#555568;--input-bg:#0d0d14;--thumb-bg:#1a1a24;}
  @media(prefers-color-scheme:light){:root{--dark:#f4f4f6;--panel:#ffffff;--border:#d8d8e0;--text:#1a1a2e;--muted:#888899;--input-bg:#eaeaf0;--thumb-bg:#dcdce8;}}
  *{margin:0;padding:0;box-sizing:border-box;}
  body{background:var(--dark);color:var(--text);font-family:'Rajdhani',sans-serif;font-size:21px;min-height:100vh;display:flex;flex-direction:column;align-items:center;padding:24px 32px;}
  h1{font-family:'Orbitron',monospace;font-weight:900;font-size:2.4rem;color:var(--red);letter-spacing:.12em;text-shadow:0 0 24px rgba(227,25,55,.45);margin-bottom:6px;}
  .sub{color:var(--muted);font-size:.9rem;letter-spacing:.08em;text-transform:uppercase;margin-bottom:20px;}
  .tabs{display:flex;gap:8px;flex-wrap:wrap;margin-bottom:20px;width:100%;max-width:1600px;}
  .tab-btn{font-family:'Orbitron',monospace;font-size:.8rem;letter-spacing:.08em;padding:11px 20px;border-radius:8px;border:1px solid var(--border);background:transparent;color:var(--muted);cursor:pointer;transition:all .15s;}
  .tab-btn.active{background:var(--red);color:#fff;border-color:var(--red);}
  .tab-panel{display:none;width:100%;max-width:1600px;}
  .tab-panel.active{display:block;}
  .card{background:var(--panel);border:1px solid var(--border);border-radius:12px;width:100%;padding:32px 40px;margin-bottom:24px;}
  .card h2{font-family:'Orbitron',monospace;font-size:.95rem;letter-spacing:.15em;color:var(--muted);margin-bottom:22px;text-transform:uppercase;}
  .usage{font-family:monospace;font-size:1rem;background:var(--input-bg);border:1px solid var(--border);border-radius:8px;padding:18px 22px;line-height:2;word-break:break-all;}
  .usage span{color:var(--red);}
  .stream-row{display:flex;justify-content:space-between;align-items:center;padding:14px 0;border-bottom:1px solid var(--border);}
  .stream-row:last-child{border-bottom:none;}
  .badge{display:inline-block;padding:4px 12px;border-radius:20px;font-size:.8rem;letter-spacing:.06em;font-family:'Orbitron',monospace;}
  .badge.streaming{background:rgba(0,200,100,.15);color:#00a852;border:1px solid rgba(0,200,100,.3);}
  .badge.starting{background:rgba(255,152,0,.12);color:#c97800;border:1px solid rgba(255,152,0,.3);}
  .badge.error{background:rgba(227,25,55,.12);color:var(--red);border:1px solid rgba(227,25,55,.3);}
  .badge.done{background:var(--input-bg);color:var(--muted);border:1px solid var(--border);}
  .empty{color:var(--muted);font-size:1rem;font-style:italic;}
  a{color:var(--red);text-decoration:none;}a:hover{text-decoration:underline;}
  .env-row{display:flex;gap:28px;flex-wrap:wrap;margin-top:6px;}
  .env-item{font-family:monospace;font-size:.9rem;color:var(--muted);}
  .env-item b{color:var(--text);}
  /* Feed tab */
  .feed-controls{display:flex;gap:12px;flex-wrap:wrap;align-items:center;margin-bottom:22px;}
  .feed-controls input{flex:1;min-width:240px;background:var(--input-bg);color:var(--text);border:1px solid var(--border);border-radius:8px;padding:12px 16px;font-family:monospace;font-size:1rem;}
  .feed-controls button{background:var(--red);color:white;border:0;border-radius:8px;padding:12px 20px;font-family:'Orbitron',monospace;letter-spacing:.08em;cursor:pointer;white-space:nowrap;font-size:.8rem;}
  .feed-status{color:var(--muted);font-size:.9rem;font-style:italic;margin-bottom:12px;min-height:1.4em;}
  .feed-grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(260px,1fr));gap:18px;}
  .feed-card{background:var(--input-bg);border:1px solid var(--border);border-radius:10px;overflow:hidden;cursor:pointer;transition:border-color .15s;}
  .feed-card:hover{border-color:var(--red);}
  .feed-card-dismiss{background:none;border:none;color:var(--muted);font-size:14px;line-height:1;cursor:pointer;padding:0 0 0 6px;flex-shrink:0;}
  .feed-card-dismiss:hover{color:var(--red);}
  .feed-thumb{width:100%;aspect-ratio:16/9;object-fit:cover;background:var(--thumb-bg);display:block;}
  .feed-info{padding:10px 13px;}
  .feed-title{font-size:.9rem;line-height:1.35;color:var(--text);margin-bottom:5px;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden;}
  .feed-dur{font-family:monospace;font-size:.78rem;color:var(--muted);}
  /* shared input style for start-stream row */
  #yt-id{flex:1;min-width:300px;background:var(--input-bg);color:var(--text);border:1px solid var(--border);border-radius:8px;padding:12px 16px;font-family:monospace;font-size:1rem;}
  select{background:var(--input-bg);color:var(--text);border:1px solid var(--border);border-radius:8px;padding:12px 16px;font-family:monospace;font-size:1rem;}
  footer{margin-top:30px;color:var(--muted);font-size:.82rem;letter-spacing:.04em;text-align:center;max-width:1600px;line-height:1.6;}
</style>
</head>
<body>
<h1>OPENCARSTREAM</h1>
<p class="sub">A third-party streaming launcher for Tesla’s in-car browser</p>

<div class="tabs">
  <button class="tab-btn active" data-tab="stream">Stream</button>
  <button class="tab-btn" data-tab="feed">YouTube</button>
  <button class="tab-btn" data-tab="twitch">Twitch</button>
  <button class="tab-btn" data-tab="pluto">Pluto TV</button>
  <button class="tab-btn" data-tab="iptv">IPTV</button>
  <button class="tab-btn" data-tab="ace">Acestream</button>
  <button class="tab-btn" data-tab="local">Local Media</button>
  <button class="tab-btn" data-tab="info">Info</button>
</div>

<!-- ── Stream tab ── -->
<div class="tab-panel active" id="tab-stream">
  <div class="card">
    <h2>Start stream</h2>
    <p style="font-size:.85rem;color:var(--muted);margin-bottom:12px;">
      Paste any YouTube, Twitch, or X/Twitter video URL — or a YouTube video ID.
    </p>
    <div style="display:flex;flex-direction:column;gap:10px;">
      <input id="yt-id" type="text" placeholder="URL or YouTube video ID">
      <div id="yt-mode-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
      <div id="yt-quality-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
      <div id="yt-sync-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
    </div>
    <div style="margin-top:10px;">
      <button id="go-stream"
              style="background:var(--red);color:white;border:0;border-radius:6px;padding:10px 16px;font-family:'Orbitron',monospace;letter-spacing:.08em;cursor:pointer;">
        OPEN STREAM
      </button>
    </div>
  </div>

  <div class="card">
    <h2>Active streams ({{stream_count}})</h2>
    {{streams_html}}
  </div>

  <div class="card">
    <h2>Configuration</h2>
    <div class="env-row">
      <div class="env-item">FPS <b>{{fps}}</b></div>
      <div class="env-item">Quality <b>{{quality}}</b></div>
      <div class="env-item">Resolution <b>{{width}}×{{height}}</b></div>
      <div class="env-item">Max streams <b>{{max_streams}}</b></div>
    <div class="env-item">Audio start delay <b>{{audio_delay_ms}} ms</b></div>
    <div class="env-item">Subscriptions <b>{{subs_status}}</b></div>
    <div class="env-item">Pluto TV langs <b>{{pluto_langs}}</b></div>
    <div class="env-item">IPTV lists <b>{{iptv_status}}</b></div>
  </div>
</div>
</div>

<!-- ── Feed tab ── -->
<div class="tab-panel" id="tab-feed">
  <div class="card">
    <h2>Playback options</h2>
    <div style="display:flex;flex-direction:column;gap:10px;">
      <div id="feed-mode-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
      <div id="feed-quality-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
      <div id="feed-sync-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
    </div>
  </div>

  <!-- Home feed panel -->
  <div class="card" id="home-card" style="display:none;">
    <h2>Home feed</h2>
    <div style="display:flex;gap:10px;flex-wrap:wrap;align-items:center;margin-bottom:14px;">
      <button id="home-load" style="background:var(--red);color:white;border:0;border-radius:8px;padding:11px 20px;font-family:'Orbitron',monospace;font-size:.8rem;letter-spacing:.08em;cursor:pointer;">SHOW HOME FEED</button>
      <button id="home-refresh" style="display:none;background:transparent;color:var(--muted);border:1px solid var(--border);border-radius:8px;padding:11px 18px;font-family:'Orbitron',monospace;font-size:.75rem;letter-spacing:.08em;cursor:pointer;">↺ REFRESH</button>
    </div>
    <div class="feed-status" id="home-status"></div>
    <div class="feed-grid" id="home-grid"></div>
    <div style="text-align:center;margin-top:14px;display:none;" id="home-more-wrap">
      <button id="home-more" style="background:transparent;color:var(--muted);border:1px solid var(--border);border-radius:6px;padding:8px 20px;font-family:'Orbitron',monospace;font-size:.7rem;letter-spacing:.08em;cursor:pointer;">LOAD MORE</button>
    </div>
  </div>

  <!-- Subscriptions panel (shown when subscriptions file is mounted) -->
  <div class="card" id="subs-card" style="display:none;">
    <h2>My subscriptions</h2>
    <div style="display:flex;gap:10px;flex-wrap:wrap;align-items:center;margin-bottom:14px;">
      <button id="subs-load" style="background:var(--red);color:white;border:0;border-radius:8px;padding:11px 20px;font-family:'Orbitron',monospace;font-size:.8rem;letter-spacing:.08em;cursor:pointer;">SHOW SUBSCRIPTIONS</button>
      <input id="subs-filter" type="text" placeholder="Filter channels…"
             style="flex:1;min-width:180px;background:var(--input-bg);color:var(--text);border:1px solid var(--border);border-radius:8px;padding:10px 14px;font-family:monospace;font-size:.95rem;display:none;">
    </div>
    <div class="feed-status" id="subs-status"></div>
    <div id="subs-list" style="display:flex;flex-direction:column;gap:0;max-height:480px;overflow-y:auto;border:1px solid var(--border);border-radius:8px;padding:0 4px;"></div>
  </div>

  <!-- YouTube search -->
  <div class="card">
    <h2>Search YouTube</h2>
    <div class="feed-controls">
      <input id="yt-search-input" type="text" placeholder="Search query…">
      <button id="yt-search-go">SEARCH</button>
    </div>
    <div class="feed-status" id="yt-search-status"></div>
    <div class="feed-grid" id="yt-search-grid"></div>
    <div style="text-align:center;margin-top:14px;display:none;" id="yt-search-more-wrap">
      <button id="yt-search-more" style="background:transparent;color:var(--muted);border:1px solid var(--border);border-radius:6px;padding:8px 20px;font-family:'Orbitron',monospace;font-size:.7rem;letter-spacing:.08em;cursor:pointer;">LOAD MORE</button>
    </div>
  </div>

  <!-- Manual channel lookup -->
  <div class="card">
    <h2 id="feed-card-title">Channel recent uploads</h2>
    <div class="feed-controls">
      <input id="feed-channel" type="text" placeholder="@channelhandle or channel URL">
      <button id="feed-go">LOAD FEED</button>
    </div>
    <div class="feed-status" id="feed-status"></div>
    <div class="feed-grid" id="feed-grid"></div>
    <div style="text-align:center;margin-top:14px;display:none;" id="feed-more-wrap">
      <button id="feed-more" style="background:transparent;color:var(--muted);border:1px solid var(--border);border-radius:6px;padding:8px 20px;font-family:'Orbitron',monospace;font-size:.7rem;letter-spacing:.08em;cursor:pointer;">LOAD MORE</button>
    </div>
  </div>
</div>

<!-- ── Twitch tab ── -->
<div class="tab-panel" id="tab-twitch">
  <div class="card">
    <h2>Playback options</h2>
    <div style="display:flex;flex-direction:column;gap:10px;">
      <div id="twitch-mode-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
      <div id="twitch-quality-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
      <div id="twitch-sync-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
    </div>
  </div>
  <div class="card">
    <h2>Live stream</h2>
    <div style="display:flex;flex-direction:column;gap:10px;">
      <input id="twitch-live-channel" type="text" placeholder="channel name (e.g. xqc)" style="background:var(--input-bg);color:var(--text);border:1px solid var(--border);border-radius:8px;padding:12px 16px;font-family:monospace;font-size:1rem;">
      <div><button id="twitch-live-go" style="background:var(--red);color:white;border:0;border-radius:8px;padding:12px 20px;font-family:'Orbitron',monospace;letter-spacing:.08em;cursor:pointer;font-size:.8rem;">WATCH LIVE</button></div>
    </div>
  </div>
  <div class="card">
    <h2>VODs</h2>
    <div style="display:flex;flex-direction:column;gap:10px;margin-bottom:14px;">
      <input id="twitch-vod-channel" type="text" placeholder="channel name" style="background:var(--input-bg);color:var(--text);border:1px solid var(--border);border-radius:8px;padding:12px 16px;font-family:monospace;font-size:1rem;">
      <div><button id="twitch-vod-go" style="background:var(--red);color:white;border:0;border-radius:8px;padding:12px 20px;font-family:'Orbitron',monospace;letter-spacing:.08em;cursor:pointer;font-size:.8rem;">LOAD VODS</button></div>
    </div>
    <div class="feed-status" id="twitch-vod-status"></div>
    <div class="feed-grid" id="twitch-vod-grid"></div>
    <div style="text-align:center;margin-top:14px;display:none;" id="twitch-vod-more-wrap">
      <button id="twitch-vod-more" style="background:transparent;color:var(--muted);border:1px solid var(--border);border-radius:6px;padding:8px 20px;font-family:'Orbitron',monospace;font-size:.7rem;letter-spacing:.08em;cursor:pointer;">LOAD MORE</button>
    </div>
  </div>
</div>

<!-- ── Pluto TV tab ── -->
<div class="tab-panel" id="tab-pluto">
  <div class="card">
    <h2>Playback options</h2>
    <div style="display:flex;flex-direction:column;gap:10px;">
      <div id="pluto-mode-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
      <div id="pluto-sync-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
      <input id="pluto-filter" type="text" placeholder="Filter channels…"
             style="background:var(--input-bg);color:var(--text);border:1px solid var(--border);border-radius:6px;padding:8px 12px;font-family:monospace;">
    </div>
  </div>
  <div class="card">
    <h2>Channels</h2>
    <div id="pluto-lang-btns" style="display:flex;gap:6px;flex-wrap:wrap;margin-bottom:14px;"></div>
    <div class="feed-status" id="pluto-status">Open this tab to load channels.</div>
    <div id="pluto-list" style="max-height:520px;overflow-y:auto;border:1px solid var(--border);border-radius:8px;padding:0 10px 10px;"></div>
  </div>
</div>

<!-- ── IPTV tab ── -->
<div class="tab-panel" id="tab-iptv">
  <div class="card">
    <h2>Playback options</h2>
    <div style="display:flex;flex-direction:column;gap:10px;">
      <div id="iptv-mode-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
      <div id="iptv-quality-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
      <div id="iptv-sync-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
    </div>
  </div>
  <div class="card">
    <h2>IPTV lists</h2>
    <div style="display:flex;gap:10px;flex-wrap:wrap;align-items:center;margin-bottom:14px;">
      <button id="iptv-prev"
              style="background:transparent;color:var(--muted);border:1px solid var(--border);border-radius:6px;padding:8px 14px;font-family:'Orbitron',monospace;font-size:.9rem;cursor:pointer;">
        ◄
      </button>
      <div id="iptv-list-name"
           style="flex:1;min-width:180px;color:var(--text);font-size:.85rem;text-align:center;padding:8px;border:1px solid var(--border);border-radius:6px;background:var(--input-bg);">
        Select a list
      </div>
      <button id="iptv-next"
              style="background:transparent;color:var(--muted);border:1px solid var(--border);border-radius:6px;padding:8px 14px;font-family:'Orbitron',monospace;font-size:.9rem;cursor:pointer;">
        ►
      </button>
      <button id="iptv-refresh"
              style="background:var(--red);color:white;border:0;border-radius:6px;padding:8px 14px;font-family:'Orbitron',monospace;font-size:.7rem;letter-spacing:.08em;cursor:pointer;">
        REFRESH
      </button>
    </div>
    <input id="iptv-filter" type="text" placeholder="Filter streams..."
           style="width:100%;background:var(--input-bg);color:var(--text);border:1px solid var(--border);border-radius:6px;padding:8px 12px;font-family:monospace;margin-bottom:12px;">
    <div class="feed-status" id="iptv-status">Open this tab to load IPTV lists.</div>
    <div id="iptv-streams"></div>
  </div>
</div>

<!-- ── Acestream tab ── -->
<div class="tab-panel" id="tab-ace">
  <div class="card">
    <h2>Playback options</h2>
    <div style="display:flex;flex-direction:column;gap:8px;">
      <div id="ace-mode-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
      <div id="ace-quality-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
      <div id="ace-sync-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
    </div>
  </div>
  <div class="card">
    <h2>Stream by content ID</h2>
    <p style="font-size:.85rem;color:var(--muted);margin-bottom:12px;">
      Enter an Acestream content ID (40-char hex) or a full
      <code style="color:var(--text);">acestream://</code> link.
      Your acestream-http-proxy must be running.
    </p>
    <div class="feed-controls">
      <input id="ace-id" type="text" placeholder="acestream://b08e… or content ID">
      <input id="ace-host" type="text" placeholder="Proxy host:port"
             style="max-width:200px;">
      <button id="ace-go">OPEN STREAM</button>
    </div>
  </div>
  <div class="card">
    <h2>Saved streams</h2>
    <div style="display:flex;gap:10px;flex-wrap:wrap;align-items:center;margin-bottom:14px;">
      <input id="ace-save-name" type="text" placeholder="Name"
             style="flex:1;min-width:140px;background:var(--input-bg);color:var(--text);border:1px solid var(--border);border-radius:6px;padding:8px 12px;font-family:monospace;">
      <input id="ace-save-id" type="text" placeholder="Content ID or acestream:// link"
             style="flex:2;min-width:220px;background:var(--input-bg);color:var(--text);border:1px solid var(--border);border-radius:6px;padding:8px 12px;font-family:monospace;">
      <button id="ace-save-btn"
              style="background:var(--red);color:white;border:0;border-radius:6px;padding:8px 14px;font-family:'Orbitron',monospace;font-size:.7rem;letter-spacing:.08em;cursor:pointer;">
        SAVE
      </button>
    </div>
    <div id="ace-saved-list"></div>
  </div>
</div>

<!-- ── Info tab ── -->
<div class="tab-panel" id="tab-local">
  <div class="card">
    <h2>Playback options</h2>
    <div style="display:flex;flex-direction:column;gap:10px;">
      <div id="local-mode-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
      <div id="local-sync-btns" style="display:flex;gap:6px;flex-wrap:wrap;"></div>
      <div>
        <button id="local-refresh"
                style="background:var(--red);color:white;border:0;border-radius:6px;padding:8px 14px;font-family:'Orbitron',monospace;font-size:.7rem;letter-spacing:.08em;cursor:pointer;">
          REFRESH LIST
        </button>
      </div>
    </div>
    <p style="font-size:.82rem;color:var(--muted);margin-top:12px;">
      Folder: <code style="color:var(--text);">{{local_media_dir}}</code>
    </p>
  </div>
  <div class="card">
    <h2>Video files</h2>
    <div class="feed-status" id="local-status">Open this tab to load local videos.</div>
    <div id="local-list"></div>
  </div>
</div>

<!-- ── Info tab ── -->
<div class="tab-panel" id="tab-info">
  <div class="card">
    <h2>API usage</h2>
    <div class="usage">
      GET /watch<span>?url=</span>https://youtube.com/watch?v=VIDEO_ID<br>
      GET /watch<span>?url=</span>https://www.twitch.tv/CHANNEL<br>
      GET /watch<span>?url=</span>https://x.com/user/status/ID<br>
      GET /watch<span>?url=</span>https://…<span>&amp;quality=720&amp;sync=1000</span><br>
      GET /feed<span>?channel=</span>@handle<span>&amp;limit=12</span>  → JSON video list<br>
      GET /local_media  → JSON local video list<br>
      GET /local_watch<span>?file=</span>relative/path.mp4<span>&amp;sync=1000</span><br>
      GET /iptv_lists  → JSON IPTV playlists from mounted folder<br>
      GET /iptv_streams<span>?list=</span>my-list<br>
      GET /subscriptions  → JSON channel list<br>
      GET /health   → JSON health check<br>
      GET /status   → JSON active streams
    </div>
  </div>
</div>

<footer>Tesla is a trademark of Tesla, Inc. OpenCarStream is unofficial and not affiliated with or endorsed by Tesla. YouTube is a trademark of Google LLC, Twitch is a trademark of Twitch Interactive, Inc., and X/Twitter is a trademark of X Corp.; OpenCarStream is not affiliated with or endorsed by any of them.</footer>
<p id="weather-text" style="margin-top:10px;color:var(--muted);font-size:.85rem;text-align:center;"></p>

<script>
  function stopStream(sid) {
    var xhr = new XMLHttpRequest();
    xhr.open("GET", "/stop_stream?sid=" + encodeURIComponent(sid), true);
    xhr.onreadystatechange = function () {
      if (xhr.readyState !== 4) return;
      window.location.reload();
    };
    xhr.send();
  }
</script>
<script>
(function () {
  // ── Tab switching ──
  var tabBtns = document.querySelectorAll(".tab-btn");
  var tabPanels = document.querySelectorAll(".tab-panel");
  Array.prototype.forEach.call(tabBtns, function (btn) {
    btn.addEventListener("click", function () {
      var target = btn.getAttribute("data-tab");
      Array.prototype.forEach.call(tabBtns, function (b) { b.classList.remove("active"); });
      Array.prototype.forEach.call(tabPanels, function (p) { p.classList.remove("active"); });
      btn.classList.add("active");
      var panel = document.getElementById("tab-" + target);
      if (panel) panel.classList.add("active");
    });
  });

  try {
  // ── Shared utilities ──
  function pad(n) { return n < 10 ? "0" + n : "" + n; }
  function fmtDuration(secs) {
    var s = parseInt(secs, 10);
    if (!s || isNaN(s)) return "";
    var h = Math.floor(s / 3600);
    var m = Math.floor((s % 3600) / 60);
    var sec = s % 60;
    if (h > 0) return h + ":" + pad(m) + ":" + pad(sec);
    return m + ":" + pad(sec);
  }
  function escHtml(s) {
    return (s || "").replace(/&/g,"&amp;").replace(/</g,"&lt;").replace(/>/g,"&gt;").replace(/"/g,"&quot;");
  }

  // ── Button group helper ──
  function createButtonGroup(containerId, options, defaultValue) {
    var container = document.getElementById(containerId);
    var state = { value: defaultValue || "" };

    options.forEach(function (opt) {
      var btn = document.createElement("button");
      btn.setAttribute("data-value", opt.value);
      btn.textContent = opt.label;
      btn.style.cssText = "font-family:'Orbitron',monospace;font-size:.7rem;" +
        "letter-spacing:.08em;padding:6px 12px;border-radius:6px;" +
        "border:1px solid var(--border);cursor:pointer;";
      btn.addEventListener("click", function () {
        state.value = opt.value;
        container.querySelectorAll("button").forEach(function (b) {
          b.style.background = b.getAttribute("data-value") === state.value
            ? "var(--red)" : "transparent";
          b.style.color = b.getAttribute("data-value") === state.value
            ? "#fff" : "var(--muted)";
        });
      });
      container.appendChild(btn);
    });

    // Set initial active state
    container.querySelectorAll("button").forEach(function (b) {
      b.style.background = b.getAttribute("data-value") === state.value
        ? "var(--red)" : "transparent";
      b.style.color = b.getAttribute("data-value") === state.value
        ? "#fff" : "var(--muted)";
    });

    return state;
  }

  // ── Mode button options (shared across tabs) ──
  var modeOptions = [
    { value: "mjpeg",  label: "MJPEG (Tesla)" },
    { value: "mp4",    label: "MP4 (native)" },
    { value: "audio",  label: "Audio only" }
  ];

  // ── Stream tab ──
  var idInput    = document.getElementById("yt-id");
  var goButton   = document.getElementById("go-stream");

  var modeSel = createButtonGroup("yt-mode-btns", modeOptions, "mjpeg");

  var qualitySel = createButtonGroup("yt-quality-btns", [
    { value: "", label: "AUTO" },
    { value: "1080", label: "1080p" },
    { value: "720", label: "720p" },
    { value: "480", label: "480p" },
    { value: "360", label: "360p" },
    { value: "240", label: "240p" },
    { value: "144", label: "144p" }
  ], "");

  var syncSel = createButtonGroup("yt-sync-btns", [
    { value: "0", label: "0s" },
    { value: "500", label: "0.5s" },
    { value: "1000", label: "1s" },
    { value: "1500", label: "1.5s" },
    { value: "2000", label: "2s" },
    { value: "2500", label: "2.5s" },
    { value: "3000", label: "3s" },
    { value: "3500", label: "3.5s" },
    { value: "4000", label: "4s" }
  ], "{{audio_delay_ms}}");

  function buildWatchUrl(videoUrl, quality, sync, mode) {
    var target = "/watch?url=" + encodeURIComponent(videoUrl);
    if (quality) target += "&quality=" + encodeURIComponent(quality);
    if (sync)    target += "&sync="    + encodeURIComponent(sync);
    if (mode && mode !== "mjpeg") target += "&mode=" + encodeURIComponent(mode);
    return target;
  }

  function resolveInputUrl(raw) {
    // Full URL (YouTube, Twitch, X/Twitter, etc.) — pass through
    if (/^https?:[/][/]/i.test(raw)) return raw;
    // Bare YouTube video ID (11 alphanum chars)
    if (/^[A-Za-z0-9_-]{11}$/.test(raw)) {
      return "https://www.youtube.com/watch?v=" + raw;
    }
    // Twitch channel shorthand: twitch:channel
    if (/^twitch:/i.test(raw)) {
      return "https://www.twitch.tv/" + raw.slice(7);
    }
    // Fallback: treat as YouTube ID anyway
    return "https://www.youtube.com/watch?v=" + raw;
  }

  function OpenCarStream() {
    var raw = (idInput.value || "").trim();
    if (!raw) { idInput.focus(); return; }
    window.location.href = buildWatchUrl(
      resolveInputUrl(raw), qualitySel.value, syncSel.value, modeSel.value
    );
  }

  goButton.addEventListener("click", OpenCarStream);
  idInput.addEventListener("keydown", function (e) {
    if ((e.key || "") === "Enter" || e.keyCode === 13) OpenCarStream();
  });

  // ── Twitch tab ──
  var twitchLiveCh   = document.getElementById("twitch-live-channel");
  var twitchLiveGo   = document.getElementById("twitch-live-go");
  var twitchVodCh    = document.getElementById("twitch-vod-channel");
  var twitchVodGo    = document.getElementById("twitch-vod-go");
  var twitchVodSt    = document.getElementById("twitch-vod-status");
  var twitchVodGrid  = document.getElementById("twitch-vod-grid");

  var twitchMode = createButtonGroup("twitch-mode-btns", modeOptions, "mjpeg");

  var twitchQuality = createButtonGroup("twitch-quality-btns", [
    { value: "", label: "AUTO" },
    { value: "1080", label: "1080p" },
    { value: "720", label: "720p" },
    { value: "480", label: "480p" },
    { value: "360", label: "360p" },
    { value: "240", label: "240p" }
  ], "");

  var twitchSync = createButtonGroup("twitch-sync-btns", [
    { value: "0", label: "0s" },
    { value: "500", label: "0.5s" },
    { value: "1000", label: "1s" },
    { value: "1500", label: "1.5s" },
    { value: "2000", label: "2s" },
    { value: "2500", label: "2.5s" },
    { value: "3000", label: "3s" },
    { value: "3500", label: "3.5s" },
    { value: "4000", label: "4s" }
  ], "{{audio_delay_ms}}");

  twitchLiveGo.addEventListener("click", function () {
    var ch = (twitchLiveCh.value || "").trim().replace(/^@/, "");
    if (!ch) { twitchLiveCh.focus(); return; }
    var url = "https://www.twitch.tv/" + ch;
    window.location.href = buildWatchUrl(url, twitchQuality.value, twitchSync.value, twitchMode.value);
  });
  twitchLiveCh.addEventListener("keydown", function (e) {
    if ((e.key || "") === "Enter" || e.keyCode === 13) twitchLiveGo.click();
  });

  var twitchVodMoreWrap = document.getElementById("twitch-vod-more-wrap");
  var twitchVodMoreBtn  = document.getElementById("twitch-vod-more");
  var twitchVodLimit    = 12;

  function loadTwitchVods(append) {
    var ch = (twitchVodCh.value || "").trim().replace(/^@/, "");
    if (!ch) { twitchVodCh.focus(); return; }
    if (!append) {
      twitchVodLimit = 12;
      twitchVodGrid.innerHTML = "";
      twitchVodMoreWrap.style.display = "none";
    }
    twitchVodSt.textContent = "Loading VODs…";
    var url = "https://www.twitch.tv/" + ch + "/videos";
    var xhr = new XMLHttpRequest();
    xhr.open("GET", "/feed?channel=" + encodeURIComponent(url) + "&limit=" + twitchVodLimit, true);
    xhr.timeout = 30000;
    xhr.onreadystatechange = function () {
      if (xhr.readyState !== 4) return;
      var data;
      try { data = JSON.parse(xhr.responseText); } catch (e) {
        twitchVodSt.textContent = "Failed to parse response."; return;
      }
      if (data.error) { twitchVodSt.textContent = "Error: " + data.error; return; }
      var videos = data.videos || [];
      if (!videos.length) { twitchVodSt.textContent = "No VODs found."; twitchVodMoreWrap.style.display = "none"; return; }
      if (append) {
        var existing = twitchVodGrid.querySelectorAll(".feed-card").length;
        videos = videos.slice(existing);
      }
      videos.forEach(function (v) {
        var card = document.createElement("div");
        card.className = "feed-card";
        var dur = fmtDuration(v.duration);
        card.innerHTML =
          '<img class="feed-thumb" src="' + (v.thumb || "") + '" loading="lazy" alt="">' +
          '<div class="feed-info">' +
          '<div class="feed-title">' + escHtml(v.title) + '</div>' +
          (dur ? '<div class="feed-dur">' + escHtml(dur) + '</div>' : '') +
          '</div>';
        card.addEventListener("click", function () {
          window.location.href = buildWatchUrl(v.url, twitchQuality.value, twitchSync.value, twitchMode.value);
        });
        twitchVodGrid.appendChild(card);
      });
      twitchVodSt.textContent = twitchVodGrid.querySelectorAll(".feed-card").length + " VODs";
      twitchVodMoreWrap.style.display = "block";
    };
    xhr.send();
  }

  twitchVodGo.addEventListener("click", function () { loadTwitchVods(false); });
  twitchVodMoreBtn.addEventListener("click", function () {
    twitchVodLimit += 12;
    loadTwitchVods(true);
  });
  twitchVodCh.addEventListener("keydown", function (e) {
    if ((e.key || "") === "Enter" || e.keyCode === 13) loadTwitchVods(false);
  });

  // ── Pluto TV tab ──
  var plutoFilter   = document.getElementById("pluto-filter");
  var plutoStatus   = document.getElementById("pluto-status");
  var plutoList     = document.getElementById("pluto-list");
  var plutoLangBtns = document.getElementById("pluto-lang-btns");

  var plutoMode = createButtonGroup("pluto-mode-btns", modeOptions, "mjpeg");

  var plutoSync = createButtonGroup("pluto-sync-btns", [
    { value: "0", label: "0s" },
    { value: "500", label: "0.5s" },
    { value: "1000", label: "1s" },
    { value: "1500", label: "1.5s" },
    { value: "2000", label: "2s" },
    { value: "2500", label: "2.5s" },
    { value: "3000", label: "3s" },
    { value: "3500", label: "3.5s" },
    { value: "4000", label: "4s" }
  ], "{{audio_delay_ms}}");

  var plutoByLang   = {};   // { lang: [channels] }
  var plutoMetaByLang = {}; // { lang: { country: "...", refresh_at: n } }
  var plutoActiveLang = null;
  var plutoLangs    = {{pluto_langs_json}};

  function renderPluto(channels) {
    plutoList.innerHTML = "";
    var lastCat = null;
    channels.forEach(function (ch) {
      if (ch.category && ch.category !== lastCat) {
        lastCat = ch.category;
        var hdr = document.createElement("div");
        hdr.style.cssText = "font-family:'Orbitron',monospace;font-size:.7rem;" +
          "letter-spacing:.12em;color:var(--muted);padding:10px 0 4px;" +
          "text-transform:uppercase;border-top:1px solid var(--border);margin-top:4px;";
        hdr.textContent = ch.category;
        plutoList.appendChild(hdr);
      }
      var row = document.createElement("div");
      row.className = "stream-row";
      row.style.cursor = "pointer";
      row.innerHTML =
        '<span style="font-size:.95rem;">' + escHtml(ch.name) + '</span>' +
        '<span style="font-family:monospace;font-size:.75rem;color:var(--muted);">LIVE →</span>';
      row.addEventListener("click", function () {
        if (ch.id && plutoActiveLang) {
          var plutoWatchUrl = "/pluto_watch?lang=" + encodeURIComponent(plutoActiveLang) +
            "&id=" + encodeURIComponent(ch.id) +
            "&sync=" + encodeURIComponent(plutoSync.value);
          if (plutoMode.value && plutoMode.value !== "mjpeg") plutoWatchUrl += "&mode=" + encodeURIComponent(plutoMode.value);
          window.location.href = plutoWatchUrl;
          return;
        }
        window.location.href = buildWatchUrl(ch.url, "", plutoSync.value, plutoMode.value);
      });
      plutoList.appendChild(row);
    });
  }

  function applyPlutoFilter() {
    var all = plutoByLang[plutoActiveLang] || [];
    var meta = plutoMetaByLang[plutoActiveLang] || {};
    var q = (plutoFilter.value || "").toLowerCase().trim();
    var filtered = q
      ? all.filter(function (c) {
          return c.name.toLowerCase().indexOf(q) !== -1 ||
                 c.category.toLowerCase().indexOf(q) !== -1;
        })
      : all;
    renderPluto(filtered);
    var activeTag = plutoActiveLang ? plutoActiveLang.toUpperCase() : "?";
    var countryTag = meta.country ? (" / " + meta.country.toUpperCase()) : "";
    var regionTag = meta.region ? (" req:" + meta.region.toUpperCase()) : "";
    var sameAs = "";
    var activeSig = all.map(function (c) { return c.id || c.name; }).join("|");
    if (activeSig) {
      Object.keys(plutoByLang).forEach(function (otherLang) {
        if (sameAs || otherLang === plutoActiveLang) return;
        var otherSig = (plutoByLang[otherLang] || [])
          .map(function (c) { return c.id || c.name; })
          .join("|");
        if (otherSig && otherSig === activeSig) {
          sameAs = otherLang.toUpperCase();
        }
      });
    }
    var sameNote = sameAs ? (" · same lineup as " + sameAs + " in your region") : "";
    plutoStatus.textContent =
      "[" + activeTag + countryTag + regionTag + "] " +
      filtered.length + (q ? " of " + all.length : "") +
      " channels (no account required)" + sameNote;
  }

  function switchPlutoLang(lang) {
    plutoActiveLang = lang;
    // Update button styles
    plutoLangBtns.querySelectorAll("button").forEach(function (b) {
      b.style.background = b.getAttribute("data-lang") === lang
        ? "var(--red)" : "transparent";
      b.style.color = b.getAttribute("data-lang") === lang
        ? "#fff" : "var(--muted)";
    });
    if (plutoByLang[lang]) {
      applyPlutoFilter();
      return;
    }
    plutoStatus.textContent = "Loading " + lang.toUpperCase() + " channels\u2026";
    plutoList.innerHTML = "";
    var xhr = new XMLHttpRequest();
    xhr.open("GET", "/pluto_channels?lang=" + encodeURIComponent(lang), true);
    xhr.timeout = 15000;
    xhr.onreadystatechange = function () {
      if (xhr.readyState !== 4) return;
      var data;
      try { data = JSON.parse(xhr.responseText); } catch (e) {
        plutoStatus.textContent = "Failed to load channels."; return;
      }
      if (data.error) { plutoStatus.textContent = "Error: " + data.error; return; }
      plutoByLang[lang] = data.channels || [];
      plutoMetaByLang[lang] = {
        country: data.country || "",
        region: data.region || "",
        xff: data.xff || "",
        refresh_at: data.refresh_at || 0
      };
      if (plutoActiveLang === lang) applyPlutoFilter();
    };
    xhr.send();
  }

  // Build language toggle buttons
  plutoLangs.forEach(function (lang) {
    var btn = document.createElement("button");
    btn.setAttribute("data-lang", lang);
    btn.textContent = lang.toUpperCase();
    btn.style.cssText = "font-family:'Orbitron',monospace;font-size:.7rem;" +
      "letter-spacing:.1em;padding:6px 14px;border-radius:6px;" +
      "border:1px solid var(--border);background:transparent;" +
      "color:var(--muted);cursor:pointer;";
    btn.addEventListener("click", function () { switchPlutoLang(lang); });
    plutoLangBtns.appendChild(btn);
  });

  // Load first language when Pluto tab is first opened
  var plutoOpened = false;
  document.querySelector('[data-tab="pluto"]').addEventListener("click", function () {
    if (plutoOpened) return;
    plutoOpened = true;
    switchPlutoLang(plutoLangs[0]);
  });

  plutoFilter.addEventListener("input", applyPlutoFilter);

  // ── IPTV tab ──
  var iptvPrevBtn   = document.getElementById("iptv-prev");
  var iptvNextBtn   = document.getElementById("iptv-next");
  var iptvListName  = document.getElementById("iptv-list-name");
  var iptvRefreshBtn= document.getElementById("iptv-refresh");
  var iptvFilter    = document.getElementById("iptv-filter");
  var iptvStatus    = document.getElementById("iptv-status");
  var iptvStreamsEl = document.getElementById("iptv-streams");

  var iptvMode = createButtonGroup("iptv-mode-btns", modeOptions, "mjpeg");

  var iptvQuality = createButtonGroup("iptv-quality-btns", [
    { value: "", label: "AUTO" },
    { value: "1080", label: "1080p" },
    { value: "720", label: "720p" },
    { value: "480", label: "480p" },
    { value: "360", label: "360p" },
    { value: "240", label: "240p" }
  ], "");

  var iptvSync = createButtonGroup("iptv-sync-btns", [
    { value: "0", label: "0s" },
    { value: "500", label: "0.5s" },
    { value: "1000", label: "1s" },
    { value: "1500", label: "1.5s" },
    { value: "2000", label: "2s" },
    { value: "2500", label: "2.5s" },
    { value: "3000", label: "3s" },
    { value: "3500", label: "3.5s" },
    { value: "4000", label: "4s" }
  ], "{{audio_delay_ms}}");

  var iptvLists = [];
  var iptvStreams = [];
  var iptvCurrentIndex = 0;

  function selectedIptvListId() {
    if (!iptvLists.length || iptvCurrentIndex < 0) return "";
    return iptvLists[iptvCurrentIndex].id || "";
  }

  function updateIptvListDisplay() {
    if (!iptvLists.length) {
      iptvListName.textContent = "No .m3u lists found";
      iptvListName.style.color = "var(--muted)";
      iptvPrevBtn.disabled = true;
      iptvNextBtn.disabled = true;
      iptvPrevBtn.style.opacity = "0.3";
      iptvNextBtn.style.opacity = "0.3";
      return;
    }
    iptvPrevBtn.disabled = false;
    iptvNextBtn.disabled = false;
    iptvPrevBtn.style.opacity = "1";
    iptvNextBtn.style.opacity = "1";
    var current = iptvLists[iptvCurrentIndex];
    iptvListName.textContent = current.name + " (" + (iptvCurrentIndex + 1) + "/" + iptvLists.length + ")";
    iptvListName.style.color = "var(--text)";
  }

  function renderIptvLists() {
    updateIptvListDisplay();
  }

  iptvPrevBtn.addEventListener("click", function () {
    if (!iptvLists.length) return;
    iptvCurrentIndex = (iptvCurrentIndex - 1 + iptvLists.length) % iptvLists.length;
    updateIptvListDisplay();
    loadIptvStreams();
  });

  iptvNextBtn.addEventListener("click", function () {
    if (!iptvLists.length) return;
    iptvCurrentIndex = (iptvCurrentIndex + 1) % iptvLists.length;
    updateIptvListDisplay();
    loadIptvStreams();
  });

  function renderIptvStreams(list) {
    var q = (iptvFilter.value || "").toLowerCase().trim();
    iptvStreamsEl.innerHTML = "";
    var visible = iptvStreams.filter(function (item) {
      if (!q) return true;
      return (item.name || "").toLowerCase().indexOf(q) !== -1;
    });
    if (!visible.length) {
      iptvStreamsEl.innerHTML = '<p class="empty">No streams match this filter.</p>';
      return;
    }
    visible.forEach(function (item) {
      var row = document.createElement("div");
      row.className = "stream-row";
      row.style.cursor = "pointer";
      row.innerHTML =
        '<span style="font-size:.95rem;">' + escHtml(item.name || item.url) + '</span>' +
        '<span style="font-family:monospace;font-size:.75rem;color:var(--muted);">OPEN \u2192</span>';
      row.addEventListener("click", function () {
        window.location.href = buildWatchUrl(item.url, iptvQuality.value, iptvSync.value, iptvMode.value);
      });
      iptvStreamsEl.appendChild(row);
    });
    iptvStatus.textContent = visible.length + " streams in " + list.name;
  }

  function loadIptvStreams() {
    var listId = selectedIptvListId();
    if (!listId) {
      iptvStatus.textContent = "No IPTV list selected.";
      iptvStreamsEl.innerHTML = "";
      return;
    }
    iptvStatus.textContent = "Loading IPTV streams...";
    iptvStreamsEl.innerHTML = "";
    iptvRefreshBtn.disabled = true;

    var xhr = new XMLHttpRequest();
    xhr.open("GET", "/iptv_streams?list=" + encodeURIComponent(listId), true);
    xhr.timeout = 15000;
    xhr.onreadystatechange = function () {
      if (xhr.readyState !== 4) return;
      iptvRefreshBtn.disabled = false;
      var data;
      try { data = JSON.parse(xhr.responseText); } catch (e) {
        iptvStatus.textContent = "Failed to parse response."; return;
      }
      if (data.error) { iptvStatus.textContent = "Error: " + data.error; return; }
      iptvStreams = data.streams || [];
      if (!iptvStreams.length) {
        iptvStatus.textContent = "No streams found in this list.";
        iptvStreamsEl.innerHTML = '<p class="empty">This list has no playable entries.</p>';
        return;
      }
      iptvFilter.value = "";
      renderIptvStreams(data.list || {name: "selected list"});
    };
    xhr.send();
  }

  function loadIptvLists(autoloadFirst) {
    iptvStatus.textContent = "Scanning IPTV lists folder...";
    iptvStreamsEl.innerHTML = "";
    iptvRefreshBtn.disabled = true;
    var xhr = new XMLHttpRequest();
    xhr.open("GET", "/iptv_lists", true);
    xhr.timeout = 10000;
    xhr.onreadystatechange = function () {
      if (xhr.readyState !== 4) return;
      iptvRefreshBtn.disabled = false;
      var data;
      try { data = JSON.parse(xhr.responseText); } catch (e) {
        iptvStatus.textContent = "Failed to parse response."; return;
      }
      if (data.error) { iptvStatus.textContent = "Error: " + data.error; return; }
      iptvLists = data.lists || [];
      renderIptvLists();
      if (!iptvLists.length) {
        iptvStatus.textContent = "No .m3u or .m3u8 files found.";
        return;
      }
      iptvStatus.textContent = iptvLists.length + " IPTV lists found";
      if (autoloadFirst) {
        iptvCurrentIndex = 0;
        updateIptvListDisplay();
        loadIptvStreams();
      }
    };
    xhr.send();
  }

  iptvRefreshBtn.addEventListener("click", function () { loadIptvLists(false); });
  iptvFilter.addEventListener("input", function () {
    if (!iptvStreams.length) return;
    var selected = iptvLists.find(function (item) { return item.id === selectedIptvListId(); }) || {name: "selected list"};
    renderIptvStreams(selected);
  });
  var iptvOpened = false;
  document.querySelector('[data-tab="iptv"]').addEventListener("click", function () {
    if (iptvOpened) return;
    iptvOpened = true;
    loadIptvLists(true);
  });

  // ── Home feed (inside YouTube tab) ──
  var homeCard     = document.getElementById("home-card");
  var homeGrid     = document.getElementById("home-grid");
  var homeStatus   = document.getElementById("home-status");
  var homeLoad     = document.getElementById("home-load");
  var homeRefresh  = document.getElementById("home-refresh");
  var homeMoreWrap = document.getElementById("home-more-wrap");
  var homeMoreBtn  = document.getElementById("home-more");
  var homeAllVideos = [];
  var homeShown    = 0;
  var HOME_PAGE    = 16;

  // Home feed reuses the feed tab's quality/sync selectors (defined below)

  function makeHomeCard(v) {
    var card = document.createElement("div");
    card.className = "feed-card";
    var dur = fmtDuration(v.duration);
    var dateStr = "";
    if (v.upload_date && v.upload_date.length === 8 && v.upload_date !== "NA") {
      dateStr = v.upload_date.slice(0,4) + "-" + v.upload_date.slice(4,6) + "-" + v.upload_date.slice(6,8);
    }
    card.innerHTML =
      '<img class="feed-thumb" src="' + (v.thumb || "") + '" loading="lazy" alt="">' +
      '<div class="feed-info">' +
      '<div style="display:flex;align-items:flex-start;gap:4px;">' +
      '<div class="feed-title" style="flex:1;">' + escHtml(v.title) + '</div>' +
      '<button class="feed-card-dismiss" title="Dismiss">✕</button>' +
      '</div>' +
      '<div style="display:flex;justify-content:space-between;align-items:center;margin-top:4px;">' +
      '<div style="font-size:.75rem;color:var(--red);font-family:Orbitron,monospace;letter-spacing:.04em;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;max-width:60%;">' + escHtml(v.channel || "") + '</div>' +
      '<div style="font-family:monospace;font-size:.75rem;color:var(--muted);white-space:nowrap;">' +
        (dateStr ? '<span style="color:var(--text);">' + escHtml(dateStr) + '</span>' + (dur ? ' · ' : '') : '') +
        (dur ? escHtml(dur) : '') +
      '</div>' +
      '</div></div>';
    card.querySelector(".feed-card-dismiss").addEventListener("click", function (e) {
      e.stopPropagation();
      card.remove();
    });
    card.addEventListener("click", function () {
      window.location.href = buildWatchUrl(v.url, feedQuality.value, feedSync.value, feedMode.value);
    });
    return card;
  }

  function renderHomePage() {
    var next = homeAllVideos.slice(homeShown, homeShown + HOME_PAGE);
    next.forEach(function (v) { homeGrid.appendChild(makeHomeCard(v)); });
    homeShown += next.length;
    homeMoreWrap.style.display = homeShown < homeAllVideos.length ? "block" : "none";
  }

  function loadHomeFeed(force) {
    homeStatus.textContent = "Loading…";
    homeLoad.style.display = "none";
    homeRefresh.style.display = "none";
    homeMoreWrap.style.display = "none";
    homeGrid.innerHTML = "";
    homeAllVideos = [];
    homeShown = 0;
    var xhr = new XMLHttpRequest();
    xhr.open("GET", "/subscriptions_feed" + (force ? "?force=1" : ""), true);
    xhr.timeout = 300000;
    xhr.onreadystatechange = function () {
      if (xhr.readyState !== 4) return;
      homeRefresh.style.display = "";
      var data;
      try { data = JSON.parse(xhr.responseText); } catch(e) {
        homeStatus.textContent = "Failed to parse response."; return;
      }
      if (data.error) { homeStatus.textContent = "Error: " + data.error; return; }
      var videos = data.videos || [];
      if (!videos.length) { homeStatus.textContent = "No videos found."; return; }
      // Server already sorted: dated newest-first, then undated by channel position.
      // Re-sort on client in case cache was built by an older version.
      homeAllVideos = videos;
      var cachedNote = data.cached ? " · cached" : "";
      var builtDate  = data.built_at ? new Date(data.built_at * 1000).toLocaleTimeString() : "";
      homeStatus.textContent = videos.length + " videos" + cachedNote + (builtDate ? " · updated " + builtDate : "");
      renderHomePage();
    };
    xhr.send();
  }

  homeMoreBtn.addEventListener("click", renderHomePage);
  homeLoad.addEventListener("click", function () { loadHomeFeed(false); });
  homeRefresh.addEventListener("click", function () { loadHomeFeed(true); });

  // ── Feed tab ──
  var feedChannel  = document.getElementById("feed-channel");
  var feedGoBtn    = document.getElementById("feed-go");
  var feedStatus   = document.getElementById("feed-status");
  var feedGrid     = document.getElementById("feed-grid");
  var feedCardTitle= document.getElementById("feed-card-title");

  var feedMode = createButtonGroup("feed-mode-btns", modeOptions, "mjpeg");

  var feedQuality = createButtonGroup("feed-quality-btns", [
    { value: "", label: "AUTO" },
    { value: "1080", label: "1080p" },
    { value: "720", label: "720p" },
    { value: "480", label: "480p" },
    { value: "360", label: "360p" },
    { value: "240", label: "240p" },
    { value: "144", label: "144p" }
  ], "");

  var feedSync = createButtonGroup("feed-sync-btns", [
    { value: "0", label: "0s" },
    { value: "500", label: "0.5s" },
    { value: "1000", label: "1s" },
    { value: "1500", label: "1.5s" },
    { value: "2000", label: "2s" },
    { value: "2500", label: "2.5s" },
    { value: "3000", label: "3s" },
    { value: "3500", label: "3.5s" },
    { value: "4000", label: "4s" }
  ], "{{audio_delay_ms}}");

  // Subscriptions
  var subsCard   = document.getElementById("subs-card");
  var subsLoad   = document.getElementById("subs-load");
  var subsFilter = document.getElementById("subs-filter");
  var subsStatus = document.getElementById("subs-status");
  var subsList   = document.getElementById("subs-list");
  var allChannels = [];

  // Probe whether subscriptions.json is mounted; show subscription + home cards if so
  (function probeSubscriptions() {
    var xhr = new XMLHttpRequest();
    xhr.open("GET", "/subscriptions", true);
    xhr.timeout = 2000;
    xhr.onreadystatechange = function () {
      if (xhr.readyState !== 4) return;
      if (xhr.status !== 503) {
        subsCard.style.display = "block";
        homeCard.style.display = "block";
      }
    };
    xhr.send();
  })();

  // ── Favorites (persisted server-side in /config/favorites.json) ─────────
  var serverFavs = [];  // set of URLs, loaded once and kept in sync

  function fetchFavs(cb) {
    var xhr = new XMLHttpRequest();
    xhr.open("GET", "/favorites", true);
    xhr.timeout = 5000;
    xhr.onreadystatechange = function () {
      if (xhr.readyState !== 4) return;
      try { serverFavs = JSON.parse(xhr.responseText).favorites || []; } catch(e) { serverFavs = []; }
      if (cb) cb();
    };
    xhr.send();
  }

  function toggleFav(url, isFav, cb) {
    var xhr = new XMLHttpRequest();
    if (isFav) {
      xhr.open("DELETE", "/favorites?url=" + encodeURIComponent(url), true);
      xhr.send();
    } else {
      xhr.open("POST", "/favorites", true);
      xhr.setRequestHeader("Content-Type", "application/json");
      xhr.send(JSON.stringify({url: url}));
    }
    xhr.onreadystatechange = function () {
      if (xhr.readyState !== 4) return;
      try { serverFavs = JSON.parse(xhr.responseText).favorites || []; } catch(e) {}
      if (cb) cb();
    };
  }

  function sortWithFavs(channels) {
    return channels.slice().sort(function(a, b) {
      var fa = serverFavs.indexOf(a.url) !== -1 ? 1 : 0;
      var fb = serverFavs.indexOf(b.url) !== -1 ? 1 : 0;
      if (fa !== fb) return fb - fa;
      return a.name.localeCompare(b.name);
    });
  }

  function renderChannelList(channels) {
    subsList.innerHTML = "";
    var sorted = sortWithFavs(channels);
    sorted.forEach(function (ch) {
      var isFav = serverFavs.indexOf(ch.url) !== -1;
      var row = document.createElement("div");
      row.className = "stream-row";
      row.style.cursor = "pointer";
      row.style.alignItems = "center";

      var star = document.createElement("span");
      star.textContent = isFav ? "★" : "☆";
      star.title = isFav ? "Remove from favorites" : "Add to favorites";
      star.style.cssText = "font-size:1.2rem;margin-right:8px;flex-shrink:0;color:" + (isFav ? "#f5c518" : "var(--muted)") + ";cursor:pointer;user-select:none;";
      star.addEventListener("click", function (e) {
        e.stopPropagation();
        var wasFav = serverFavs.indexOf(ch.url) !== -1;
        toggleFav(ch.url, wasFav, function () { applyFilter(); });
      });

      var label = document.createElement("a");
      label.style.cssText = "color:var(--text);font-size:.95rem;flex:1;";
      label.textContent = ch.name;

      var arrow = document.createElement("span");
      arrow.style.cssText = "font-family:monospace;font-size:.75rem;color:var(--muted);";
      arrow.textContent = "LOAD →";

      row.appendChild(star);
      row.appendChild(label);
      row.appendChild(arrow);

      row.addEventListener("click", function () {
        feedChannel.value = ch.url;
        feedCardTitle.textContent = ch.name + " — recent uploads";
        loadFeed();
        feedGrid.scrollIntoView({behavior: "smooth", block: "start"});
      });
      subsList.appendChild(row);
    });
  }

  function applyFilter() {
    var q = (subsFilter.value || "").toLowerCase().trim();
    if (!q) { renderChannelList(allChannels); return; }
    renderChannelList(allChannels.filter(function (ch) {
      return ch.name.toLowerCase().indexOf(q) !== -1;
    }));
  }

  subsLoad.addEventListener("click", function () {
    subsStatus.textContent = "Loading subscriptions…";
    subsList.innerHTML = "";
    subsFilter.style.display = "none";
    subsLoad.disabled = true;
    var xhr = new XMLHttpRequest();
    xhr.open("GET", "/subscriptions", true);
    xhr.timeout = 45000;
    xhr.onreadystatechange = function () {
      if (xhr.readyState !== 4) return;
      subsLoad.disabled = false;
      var data;
      try { data = JSON.parse(xhr.responseText); } catch (e) {
        subsStatus.textContent = "Failed to parse response."; return;
      }
      if (data.error) {
        subsStatus.textContent = "Error: " + data.error; return;
      }
      allChannels = data.channels || [];
      if (!allChannels.length) {
        subsStatus.textContent = "No subscriptions found."; return;
      }
      var syncedAt = data.synced_at ? " · synced " + data.synced_at.slice(0, 10) : "";
      subsStatus.textContent = allChannels.length + " channels" + syncedAt;
      subsFilter.style.display = "";
      subsFilter.value = "";
      fetchFavs(function () { renderChannelList(allChannels); });
    };
    xhr.send();
  });

  subsFilter.addEventListener("input", applyFilter);

  // ── Weather (IP-based, no geolocation API needed) ──────────────────────
  (function initWeather() {
    var WMO_ICONS = {
      0:"☀️",1:"🌤️",2:"⛅",3:"☁️",45:"🌫️",48:"🌫️",
      51:"🌦️",53:"🌦️",55:"🌧️",61:"🌧️",63:"🌧️",65:"🌧️",
      71:"🌨️",73:"🌨️",75:"❄️",80:"🌦️",81:"🌧️",82:"⛈️",
      95:"⛈️",96:"⛈️",99:"⛈️"
    };
    var WMO_DESC = {
      0:"Clear sky",1:"Mainly clear",2:"Partly cloudy",3:"Overcast",
      45:"Fog",48:"Icy fog",51:"Light drizzle",53:"Drizzle",55:"Heavy drizzle",
      61:"Light rain",63:"Rain",65:"Heavy rain",71:"Light snow",73:"Snow",
      75:"Heavy snow",80:"Showers",81:"Rain showers",82:"Violent showers",
      95:"Thunderstorm",96:"Thunderstorm w/ hail",99:"Thunderstorm w/ heavy hail"
    };

    function showWeatherText(temp, code, city) {
      var el = document.getElementById("weather-text");
      if (!el) return;
      var icon = WMO_ICONS[code] || "🌡️";
      var desc = WMO_DESC[code] || "";
      el.textContent = icon + " " + Math.round(temp) + "°C  " + desc + (city ? "  ·  " + city : "");
    }

    function fetchWeather(lat, lon, city) {
      var xhr = new XMLHttpRequest();
      xhr.open("GET", "https://api.open-meteo.com/v1/forecast?latitude=" + lat +
               "&longitude=" + lon + "&current_weather=true&forecast_days=1", true);
      xhr.timeout = 8000;
      xhr.onreadystatechange = function() {
        if (xhr.readyState !== 4 || xhr.status !== 200) return;
        try {
          var d = JSON.parse(xhr.responseText);
          var cw = d.current_weather;
          showWeatherText(cw.temperature, cw.weathercode, city);
        } catch(e) {}
      };
      xhr.send();
    }

    // Use IP geolocation — works over HTTP, no browser permission needed
    var xhr = new XMLHttpRequest();
    xhr.open("GET", "https://ipapi.co/json/", true);
    xhr.timeout = 6000;
    xhr.onreadystatechange = function() {
      if (xhr.readyState !== 4 || xhr.status !== 200) return;
      try {
        var d = JSON.parse(xhr.responseText);
        if (d.latitude && d.longitude) fetchWeather(d.latitude, d.longitude, d.city || "");
      } catch(e) {}
    };
    xhr.send();
  })();

  var feedMoreWrap = document.getElementById("feed-more-wrap");
  var feedMoreBtn  = document.getElementById("feed-more");

  // ── YouTube search ──
  var ytSearchInput    = document.getElementById("yt-search-input");
  var ytSearchGoBtn    = document.getElementById("yt-search-go");
  var ytSearchStatus   = document.getElementById("yt-search-status");
  var ytSearchGrid     = document.getElementById("yt-search-grid");
  var ytSearchMoreWrap = document.getElementById("yt-search-more-wrap");
  var ytSearchMoreBtn  = document.getElementById("yt-search-more");
  var ytSearchLimit    = 12;

  function appendSearchCards(videos) {
    videos.forEach(function (v) {
      var card = document.createElement("div");
      card.className = "feed-card";
      var dur = fmtDuration(v.duration);
      card.innerHTML =
        '<img class="feed-thumb" src="' + (v.thumb || "") + '" loading="lazy" alt="">' +
        '<div class="feed-info">' +
        '<div class="feed-title">' + escHtml(v.title) + '</div>' +
        (dur ? '<div class="feed-dur">' + escHtml(dur) + '</div>' : '') +
        '</div>';
      card.addEventListener("click", function () {
        window.location.href = buildWatchUrl(v.url, feedQuality.value, feedSync.value, feedMode.value);
      });
      ytSearchGrid.appendChild(card);
    });
  }

  function runYtSearch(append) {
    var q = (ytSearchInput.value || "").trim();
    if (!q) { ytSearchInput.focus(); return; }
    if (!append) {
      ytSearchLimit = 12;
      ytSearchGrid.innerHTML = "";
      ytSearchMoreWrap.style.display = "none";
    }
    ytSearchStatus.textContent = append ? "Loading more…" : "Searching…";
    var xhr = new XMLHttpRequest();
    xhr.open("GET", "/ytsearch?q=" + encodeURIComponent(q) + "&limit=" + ytSearchLimit, true);
    xhr.timeout = 30000;
    xhr.onreadystatechange = function () {
      if (xhr.readyState !== 4) return;
      if (xhr.status < 200 || xhr.status >= 300) {
        ytSearchStatus.textContent = "Error: " + xhr.status;
        return;
      }
      var data;
      try { data = JSON.parse(xhr.responseText); } catch (e) {
        ytSearchStatus.textContent = "Failed to parse response.";
        return;
      }
      if (data.error) {
        ytSearchStatus.textContent = "Error: " + data.error;
        return;
      }
      var videos = data.videos || [];
      if (!videos.length) {
        ytSearchStatus.textContent = "No results found.";
        return;
      }
      if (append) {
        var existing = ytSearchGrid.querySelectorAll(".feed-card").length;
        appendSearchCards(videos.slice(existing));
      } else {
        appendSearchCards(videos);
      }
      ytSearchStatus.textContent = ytSearchGrid.querySelectorAll(".feed-card").length + " results";
      ytSearchMoreWrap.style.display = "block";
    };
    xhr.send();
  }

  ytSearchGoBtn.addEventListener("click", function () { runYtSearch(false); });
  ytSearchInput.addEventListener("keydown", function (e) {
    if (e.key === "Enter") runYtSearch(false);
  });
  ytSearchMoreBtn.addEventListener("click", function () {
    ytSearchLimit += 12;
    runYtSearch(true);
  });
  var feedLimit    = 12;

  function appendFeedCards(videos) {
    videos.forEach(function (v) {
      var card = document.createElement("div");
      card.className = "feed-card";
      var dur = fmtDuration(v.duration);
      card.innerHTML =
        '<img class="feed-thumb" src="' + (v.thumb || "") + '" loading="lazy" alt="">' +
        '<div class="feed-info">' +
        '<div class="feed-title">' + escHtml(v.title) + '</div>' +
        (dur ? '<div class="feed-dur">' + escHtml(dur) + '</div>' : '') +
        '</div>';
      card.addEventListener("click", function () {
        window.location.href = buildWatchUrl(v.url, feedQuality.value, feedSync.value, feedMode.value);
      });
      feedGrid.appendChild(card);
    });
  }

  function loadFeed(append) {
    var ch = (feedChannel.value || "").trim();
    if (!ch) { feedChannel.focus(); return; }
    if (!append) {
      feedLimit = 12;
      feedGrid.innerHTML = "";
      feedMoreWrap.style.display = "none";
    }
    feedStatus.textContent = "Loading…";
    var xhr = new XMLHttpRequest();
    xhr.open("GET", "/feed?channel=" + encodeURIComponent(ch) + "&limit=" + feedLimit, true);
    xhr.timeout = 30000;
    xhr.onreadystatechange = function () {
      if (xhr.readyState !== 4) return;
      if (xhr.status < 200 || xhr.status >= 300) {
        feedStatus.textContent = "Error: " + xhr.status;
        return;
      }
      var data;
      try { data = JSON.parse(xhr.responseText); } catch (e) {
        feedStatus.textContent = "Failed to parse response.";
        return;
      }
      if (data.error) {
        feedStatus.textContent = "Error: " + data.error;
        return;
      }
      var videos = data.videos || [];
      if (!videos.length) {
        feedStatus.textContent = "No videos found for that channel.";
        feedMoreWrap.style.display = "none";
        return;
      }
      if (append) {
        var existing = feedGrid.querySelectorAll(".feed-card").length;
        appendFeedCards(videos.slice(existing));
      } else {
        appendFeedCards(videos);
      }
      feedStatus.textContent = feedGrid.querySelectorAll(".feed-card").length + " videos";
      feedMoreWrap.style.display = "block";
    };
    xhr.send();
  }

  feedMoreBtn.addEventListener("click", function () {
    feedLimit += 12;
    loadFeed(true);
  });

  feedGoBtn.addEventListener("click", loadFeed);
  feedChannel.addEventListener("keydown", function (e) {
    if ((e.key || "") === "Enter" || e.keyCode === 13) loadFeed();
  });

  // ── Acestream tab ──
  var aceIdInput  = document.getElementById("ace-id");
  var aceHost     = document.getElementById("ace-host");
  var aceGo       = document.getElementById("ace-go");
  var aceSaveName = document.getElementById("ace-save-name");
  var aceSaveId   = document.getElementById("ace-save-id");
  var aceSaveBtn  = document.getElementById("ace-save-btn");
  var aceSavedList= document.getElementById("ace-saved-list");

  var aceMode = createButtonGroup("ace-mode-btns", modeOptions, "mjpeg");

  var aceQuality = createButtonGroup("ace-quality-btns", [
    { value: "", label: "AUTO" },
    { value: "1080", label: "1080p" },
    { value: "720", label: "720p" },
    { value: "480", label: "480p" },
    { value: "360", label: "360p" }
  ], "");

  var aceSync = createButtonGroup("ace-sync-btns", [
    { value: "0", label: "0s" },
    { value: "500", label: "0.5s" },
    { value: "1000", label: "1s" },
    { value: "1500", label: "1.5s" },
    { value: "2000", label: "2s" },
    { value: "2500", label: "2.5s" },
    { value: "3000", label: "3s" },
    { value: "3500", label: "3.5s" },
    { value: "4000", label: "4s" }
  ], "{{audio_delay_ms}}");

  // Persist proxy host in localStorage; streams are stored server-side
  var ACE_HOST_KEY = "ace_proxy_host";

  aceHost.value = localStorage.getItem(ACE_HOST_KEY) || "192.168.1.7:6878";
  aceHost.addEventListener("change", function () {
    localStorage.setItem(ACE_HOST_KEY, aceHost.value.trim());
  });

  function aceContentId(raw) {
    raw = (raw || "").trim();
    // acestream://HASH → extract hash
    if (/^acestream:[/][/]/i.test(raw)) raw = raw.slice(12);
    // Full URL → extract id param
    if (/^https?:[/][/]/i.test(raw)) {
      var m = raw.match(/[?&]id=([a-f0-9]{40})/i);
      if (m) return m[1];
    }
    return raw;
  }

  function buildAceUrl(raw) {
    var cid = aceContentId(raw);
    if (!cid) return null;
    var host = (aceHost.value || "").trim() || "192.168.1.7:6878";
    return "http://" + host + "/ace/getstream?id=" + cid;
  }

  function openAceStream() {
    var raw = (aceIdInput.value || "").trim();
    if (!raw) { aceIdInput.focus(); return; }
    var url = buildAceUrl(raw);
    if (!url) { aceIdInput.focus(); return; }
    localStorage.setItem(ACE_HOST_KEY, (aceHost.value || "").trim());
    window.location.href = buildWatchUrl(url, aceQuality.value, aceSync.value, aceMode.value);
  }

  aceGo.addEventListener("click", openAceStream);
  aceIdInput.addEventListener("keydown", function (e) {
    if ((e.key || "") === "Enter" || e.keyCode === 13) openAceStream();
  });

  // Saved streams (server-side)
  function renderSaved(list) {
    aceSavedList.innerHTML = "";
    if (!list || !list.length) {
      aceSavedList.innerHTML = '<p class="empty">No saved streams yet.</p>';
      return;
    }
    list.forEach(function (item, idx) {
      var row = document.createElement("div");
      row.className = "stream-row";
      row.innerHTML =
        '<span style="cursor:pointer;flex:1;" data-idx="' + idx + '">' +
        escHtml(item.name) + '</span>' +
        '<span style="font-family:monospace;font-size:.75rem;color:var(--muted);margin-right:12px;">' +
        escHtml(item.id.slice(0, 12)) + '…</span>' +
        '<button data-del="' + idx + '" style="background:transparent;border:1px solid var(--border);' +
        'color:var(--muted);border-radius:4px;padding:2px 8px;cursor:pointer;font-size:.75rem;">✕</button>';
      row.querySelector("[data-idx]").addEventListener("click", function () {
        var url = buildAceUrl(item.id);
        if (url) window.location.href = buildWatchUrl(url, aceQuality.value, aceSync.value, aceMode.value);
      });
      row.querySelector("[data-del]").addEventListener("click", function (e) {
        e.stopPropagation();
        var xhr = new XMLHttpRequest();
        xhr.open("DELETE", "/ace_streams?idx=" + idx, true);
        xhr.onload = function () {
          try { renderSaved(JSON.parse(xhr.responseText).streams); } catch(ex) {}
        };
        xhr.send();
      });
      aceSavedList.appendChild(row);
    });
  }

  function fetchSaved() {
    var xhr = new XMLHttpRequest();
    xhr.open("GET", "/ace_streams", true);
    xhr.onload = function () {
      try { renderSaved(JSON.parse(xhr.responseText).streams); } catch(ex) {}
    };
    xhr.send();
  }

  aceSaveBtn.addEventListener("click", function () {
    var name = (aceSaveName.value || "").trim();
    var raw  = (aceSaveId.value  || "").trim();
    if (!name || !raw) return;
    var cid = aceContentId(raw);
    if (!cid) return;
    var xhr = new XMLHttpRequest();
    xhr.open("POST", "/ace_streams", true);
    xhr.setRequestHeader("Content-Type", "application/json");
    xhr.onload = function () {
      try { renderSaved(JSON.parse(xhr.responseText).streams); } catch(ex) {}
    };
    aceSaveName.value = "";
    aceSaveId.value   = "";
    xhr.send(JSON.stringify({name: name, id: cid}));
  });

  fetchSaved();

  // ── Local Media tab ──
  var localRefresh = document.getElementById("local-refresh");
  var localStatus  = document.getElementById("local-status");
  var localList    = document.getElementById("local-list");

  var localMode = createButtonGroup("local-mode-btns", modeOptions, "mjpeg");

  var localSync = createButtonGroup("local-sync-btns", [
    { value: "0", label: "0s" },
    { value: "500", label: "0.5s" },
    { value: "1000", label: "1s" },
    { value: "1500", label: "1.5s" },
    { value: "2000", label: "2s" },
    { value: "2500", label: "2.5s" },
    { value: "3000", label: "3s" },
    { value: "3500", label: "3.5s" },
    { value: "4000", label: "4s" }
  ], "{{local_media_video_delay_ms}}");

  var localCurrentDir = "";

  function renderLocalBrowser(data) {
    localList.innerHTML = "";
    var folders = data.folders || [];
    var files = data.files || [];
    var currentDir = data.current_dir || "";

    // Breadcrumb
    var crumb = document.createElement("div");
    crumb.style.cssText = "font-size:.8rem;color:var(--muted);margin-bottom:8px;display:flex;flex-wrap:wrap;gap:4px;align-items:center;";
    var parts = currentDir ? currentDir.split("/") : [];
    var rootSpan = document.createElement("span");
    rootSpan.textContent = "\\uD83D\\uDCC1 /";
    rootSpan.style.cssText = "cursor:pointer;color:var(--accent);";
    rootSpan.addEventListener("click", function () { loadLocalDir(""); });
    crumb.appendChild(rootSpan);
    parts.forEach(function (part, i) {
      var sep = document.createElement("span");
      sep.textContent = " / ";
      crumb.appendChild(sep);
      var sp = document.createElement("span");
      sp.textContent = part;
      var dirPath = parts.slice(0, i + 1).join("/");
      if (i < parts.length - 1) {
        sp.style.cssText = "cursor:pointer;color:var(--accent);";
        sp.addEventListener("click", (function(d){ return function(){ loadLocalDir(d); }; })(dirPath));
      } else {
        sp.style.color = "var(--text)";
      }
      crumb.appendChild(sp);
    });
    localList.appendChild(crumb);

    if (!folders.length && !files.length) {
      var empty = document.createElement("p");
      empty.className = "empty";
      empty.textContent = "No video files or subfolders here.";
      localList.appendChild(empty);
      return;
    }

    // Folders
    folders.forEach(function (item) {
      var row = document.createElement("div");
      row.className = "stream-row";
      row.style.cursor = "pointer";
      row.innerHTML =
        '<span style="font-size:.95rem;">\\uD83D\\uDCC2 ' + escHtml(item.name) + '</span>' +
        '<span style="font-family:monospace;font-size:.75rem;color:var(--muted);">OPEN \u2192</span>';
      row.addEventListener("click", function () { loadLocalDir(item.path); });
      localList.appendChild(row);
    });

    // Files
    files.forEach(function (item) {
      var row = document.createElement("div");
      row.className = "stream-row";
      row.style.cursor = "pointer";
      row.innerHTML =
        '<span style="font-size:.95rem;">\\uD83C\\uDFA5 ' + escHtml(item.name) + '</span>' +
        '<span style="font-family:monospace;font-size:.75rem;color:var(--muted);">PLAY \u2192</span>';
      row.addEventListener("click", function () {
        var localUrl = "/local_watch?file=" + encodeURIComponent(item.path) +
          "&sync=" + encodeURIComponent(localSync.value);
        if (localMode.value && localMode.value !== "mjpeg") localUrl += "&mode=" + encodeURIComponent(localMode.value);
        window.location.href = localUrl;
      });
      localList.appendChild(row);
    });
  }

  function loadLocalDir(dir) {
    localCurrentDir = dir || "";
    localStatus.textContent = "Loading…";
    localList.innerHTML = "";
    var xhr = new XMLHttpRequest();
    xhr.open("GET", "/local_media" + (dir ? "?dir=" + encodeURIComponent(dir) : ""), true);
    xhr.timeout = 10000;
    xhr.onreadystatechange = function () {
      if (xhr.readyState !== 4) return;
      var data;
      try { data = JSON.parse(xhr.responseText); } catch (e) {
        localStatus.textContent = "Failed to parse response."; return;
      }
      if (data.error) { localStatus.textContent = "Error: " + data.error; return; }
      var total = (data.folders || []).length + (data.files || []).length;
      localStatus.textContent = total + " item" + (total !== 1 ? "s" : "");
      renderLocalBrowser(data);
    };
    xhr.send();
  }

  localRefresh.addEventListener("click", function () { loadLocalDir(localCurrentDir); });
  var localOpened = false;
  document.querySelector('[data-tab="local"]').addEventListener("click", function () {
    if (localOpened) return;
    localOpened = true;
    loadLocalDir("");
  });
  } catch(e) { /* init error — non-fatal */ }
})();
</script>
</body></html>"""

WATCH_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>OpenCarStream Watch</title>
<style>
  @import url('https://fonts.googleapis.com/css2?family=Orbitron:wght@700;900&family=Rajdhani:wght@300;500&display=swap');
  :root{--red:#e31937;--dark:#090909;--panel:#111117;--border:#252530;--text:#e0e0ee;}
  @media(prefers-color-scheme:light){:root{--dark:#f4f4f6;--panel:#ffffff;--border:#d8d8e0;--text:#1a1a2e;}}
  *{margin:0;padding:0;box-sizing:border-box;}
  body{background:var(--dark);color:var(--text);font-family:'Rajdhani',sans-serif;min-height:100vh;display:flex;flex-direction:column;align-items:center;padding:16px;}
  .top{width:100%;max-width:1280px;display:flex;justify-content:space-between;align-items:center;margin-bottom:10px;gap:12px;flex-wrap:wrap;}
  .title{font-family:'Orbitron',monospace;letter-spacing:.1em;color:var(--red);font-size:1rem;}
  .back{color:var(--red);text-decoration:none;font-family:monospace;}
  .wrap{width:100%;max-width:1280px;background:var(--panel);border:1px solid var(--border);border-radius:10px;padding:10px;}
  img{width:100%;height:auto;display:block;background:black;border-radius:8px;}
  audio{width:100%;margin-top:10px;}
  .diag{margin-top:10px;padding:10px 12px;border:1px solid var(--border);border-radius:8px;font-family:monospace;font-size:.85rem;line-height:1.4;white-space:pre-wrap;color:#f0b5bf;background:#160d11;display:none;}
  .seek-bar{display:flex;align-items:center;gap:10px;margin-top:10px;flex-wrap:wrap;}
  .seek-btn{background:var(--panel);border:1px solid var(--border);color:var(--text);font-family:'Rajdhani',sans-serif;font-size:1rem;font-weight:500;padding:6px 14px;border-radius:6px;cursor:pointer;transition:border-color .15s,color .15s;}
  .seek-btn:hover{border-color:var(--red);color:var(--red);}
  .seek-btn.active{border-color:var(--red);color:var(--red);}
  .seek-pending{font-family:monospace;font-size:.9rem;color:var(--red);min-width:80px;}
  .seek-cancel{background:none;border:none;color:#888;font-size:.8rem;cursor:pointer;text-decoration:underline;padding:0;}
  .elapsed{font-family:monospace;font-size:1rem;color:var(--text);margin-left:auto;letter-spacing:.05em;}
  .live-badge{font-family:'Orbitron',monospace;font-size:.65rem;letter-spacing:.12em;color:#fff;background:var(--red);padding:2px 7px;border-radius:3px;text-transform:uppercase;margin-left:auto;display:none;}
  .resume-banner{margin-top:10px;padding:10px 14px;background:#1a1200;border:1px solid #6b4f00;border-radius:6px;font-size:.9rem;display:flex;align-items:center;gap:12px;flex-wrap:wrap;}
  .resume-banner a{color:#f5c518;font-weight:600;cursor:pointer;text-decoration:underline;}
  .resume-banner .dismiss{color:#888;font-size:.8rem;cursor:pointer;text-decoration:underline;background:none;border:none;}
  .stream-title{font-size:.95rem;color:var(--text);font-family:'Rajdhani',sans-serif;font-weight:500;padding:8px 4px 2px;letter-spacing:.02em;min-height:1.4em;}
  .sync-bar{display:flex;align-items:center;gap:8px;margin-top:8px;flex-wrap:wrap;padding:8px 4px;border-top:1px solid var(--border);}
  .sync-label{font-family:'Orbitron',monospace;font-size:.65rem;letter-spacing:.1em;color:var(--muted);text-transform:uppercase;}
  .sync-btn{background:var(--panel);border:1px solid var(--border);color:var(--text);font-family:'Rajdhani',sans-serif;font-size:1rem;font-weight:500;padding:6px 14px;border-radius:6px;cursor:pointer;}
  .sync-btn:hover{border-color:var(--red);color:var(--red);}
  .sync-val{font-family:monospace;font-size:.95rem;color:var(--red);min-width:60px;text-align:center;}
</style>
</head>
<body>
  <div class="top">
    <div class="title">MJPEG + AUDIO</div>
    <a class="back" href="/">← Back</a>
  </div>
  <div class="wrap">
    <img id="mjpeg" alt="Live MJPEG stream">
    <div id="stream-title" class="stream-title"></div>
    <audio id="audio" controls autoplay playsinline></audio>
    <div class="sync-bar">
      <span class="sync-label">Audio delay</span>
      <button class="sync-btn" data-delta="-0.5">−0.5s</button>
      <button class="sync-btn" data-delta="-0.1">−0.1s</button>
      <span id="sync-val" class="sync-val">0.0s</span>
      <button class="sync-btn" data-delta="0.1">+0.1s</button>
      <button class="sync-btn" data-delta="0.5">+0.5s</button>
    </div>
    <div class="seek-bar">
      <span class="sync-label" style="margin-right:4px;">Video</span>
      <button class="seek-btn" data-mins="-10">-10 min</button>
      <button class="seek-btn" data-mins="1">+1 min</button>
      <button class="seek-btn" data-mins="5">+5 min</button>
      <button class="seek-btn" data-mins="10">+10 min</button>
      <span id="seek-pending" class="seek-pending"></span>
      <button id="seek-cancel" class="seek-cancel" style="display:none">cancel</button>
      <span id="live-badge" class="live-badge">● Live</span>
      <span id="elapsed" class="elapsed">0:00:00</span>
    </div>
    <div id="resume-banner" class="resume-banner" style="display:none">
      <span id="resume-text"></span>
      <a id="resume-yes">Resume</a>
      <button class="dismiss" id="resume-no">dismiss</button>
    </div>
    <div id="diag" class="diag"></div>
  </div>
<script>
(function () {
  var sid = "{{stream_id}}";
  var syncMs = "{{sync_ms}}";
  var videoUrl = "{{video_url}}";
  var videoQuality = "{{video_quality}}";
  var localFile = "{{local_file}}";
  if (!sid) {
    window.location.href = "/";
    return;
  }
  var q = "?sid=" + encodeURIComponent(sid) + "&sync=" + encodeURIComponent(syncMs);
  var img = document.getElementById("mjpeg");
  var audio = document.getElementById("audio");
  var diag = document.getElementById("diag");
  var seekPending  = document.getElementById("seek-pending");
  var seekCancel   = document.getElementById("seek-cancel");
  var elapsedEl    = document.getElementById("elapsed");
  var liveBadgeEl  = document.getElementById("live-badge");
  var resumeBanner = document.getElementById("resume-banner");
  var resumeText   = document.getElementById("resume-text");
  var resumeYes    = document.getElementById("resume-yes");
  var resumeNo     = document.getElementById("resume-no");

  // Start audio first so its pipeline is already running and buffered.
  audio.src = "/audio?sid=" + encodeURIComponent(sid);
  audio.preload = "auto";
  audio.muted = false;
  audio.volume = 1.0;
  try {
    var p = audio.play();
    if (p && typeof p.catch === "function") p.catch(function () {});
  } catch (e) {}

  // Some browsers (including embedded WebViews) may block autoplay without
  // interaction. Retry on first user gesture.
  var retryPlay = function () {
    try {
      var p2 = audio.play();
      if (p2 && typeof p2.catch === "function") p2.catch(function () {});
    } catch (e) {}
    window.removeEventListener("click", retryPlay, true);
    window.removeEventListener("touchstart", retryPlay, true);
    window.removeEventListener("keydown", retryPlay, true);
  };
  window.addEventListener("click", retryPlay, true);
  window.addEventListener("touchstart", retryPlay, true);
  window.addEventListener("keydown", retryPlay, true);

  audio.addEventListener("loadedmetadata", function () {
    if (!isFinite(audio.duration)) {
      if (liveBadgeEl) liveBadgeEl.style.display = "inline-block";
      if (elapsedEl)   elapsedEl.style.display    = "none";
    }
  });

  // ── Real-time audio delay control ───────────────────────────────────────
  var syncValEl   = document.getElementById("sync-val");
  // Start display at the server-configured initial delay
  var audioDelayS = parseFloat(syncMs) / 1000 || 0;
  var pauseTimer  = null;

  function updateSyncDisplay() {
    syncValEl.textContent = (audioDelayS >= 0 ? "+" : "") + audioDelayS.toFixed(1) + "s";
  }
  updateSyncDisplay();

  function resumeAudio() {
    if (audio.paused) {
      try { var p = audio.play(); if (p && p.catch) p.catch(function(){}); } catch(e) {}
    }
  }

  var rateTimer = null;
  function applyAudioDelta(deltaS) {
    clearTimeout(pauseTimer);
    clearTimeout(rateTimer);
    audio.playbackRate = 1.0;
    audioDelayS = Math.round((audioDelayS + deltaS) * 10) / 10;
    updateSyncDisplay();
    var isLive = !isFinite(audio.duration);
    if (deltaS > 0) {
      // Audio plays later → pause for deltaS then resume
      audio.pause();
      pauseTimer = setTimeout(resumeAudio, Math.round(deltaS * 1000));
    } else {
      // Audio plays earlier
      if (!isLive) {
        // VOD: skip the audio forward
        audio.currentTime = Math.max(0, audio.currentTime + (-deltaS));
        resumeAudio();
      } else {
        // Live: can't seek, so play at 2x for |deltaS| seconds. That
        // advances audio by |deltaS| seconds of real-time content,
        // undoing prior positive offsets (and going negative further).
        resumeAudio();
        audio.playbackRate = 2.0;
        rateTimer = setTimeout(function () {
          audio.playbackRate = 1.0;
        }, Math.round((-deltaS) * 1000));
      }
    }
  }

  document.querySelectorAll(".sync-btn").forEach(function (btn) {
    btn.addEventListener("click", function () {
      applyAudioDelta(parseFloat(btn.getAttribute("data-delta")));
    });
  });

  // Always request video immediately; server-side frame buffering applies
  // sync_ms without skipping content from the beginning.
  img.src = "/stream" + q;

  function showDiag(message) {
    diag.style.display = "block";
    diag.textContent = message;
  }

  img.addEventListener("error", function () {
    var xhr = new XMLHttpRequest();
    xhr.open("GET", "/stream_status?sid=" + encodeURIComponent(sid), true);
    xhr.onreadystatechange = function () {
      if (xhr.readyState !== 4) return;
      if (xhr.status < 200 || xhr.status >= 300) {
        showDiag("Video stream failed to load and diagnostics request failed.");
        return;
      }
      try {
        var data = JSON.parse(xhr.responseText);
        var msg = [
          "Video stream failed to load.",
          "status: " + (data.status || "unknown"),
          "error: " + (data.error || "n/a"),
          "detail: " + (data.error_detail || "n/a")
        ].join("\\n");
        showDiag(msg);
      } catch (err) {
        showDiag("Video stream failed to load and diagnostics parse failed.");
      }
    };
    xhr.send();
  });

  // ── Seek controls ────────────────────────────────────────────────────────
  // Read seek offset already applied (so accumulated offset stays correct
  // if the user seeks multiple times).
  var params = new URLSearchParams(window.location.search);
  var baseSeekS = parseInt("{{seek_s}}", 10) || parseInt(params.get("seek") || "0", 10) || 0;
  var pendingOffsetS = 0;
  var seekTimer = null;
  var countdownInterval = null;
  var SEEK_DEBOUNCE_MS = 3000;

  function fmtOffset(s) {
    var m = Math.floor(s / 60);
    var sec = s % 60;
    return "+" + m + "m" + (sec ? sec + "s" : "");
  }

  function startSeekTimer() {
    clearTimeout(seekTimer);
    clearInterval(countdownInterval);
    var countdown = SEEK_DEBOUNCE_MS / 1000;
    seekPending.textContent = fmtOffset(pendingOffsetS) + " (seeking in " + countdown + "s)";
    seekCancel.style.display = "inline";

    countdownInterval = setInterval(function () {
      countdown--;
      if (countdown > 0) {
        seekPending.textContent = fmtOffset(pendingOffsetS) + " (seeking in " + countdown + "s)";
      }
    }, 1000);

    seekTimer = setTimeout(function () {
      clearInterval(countdownInterval);
      var targetSeek = Math.max(0, baseSeekS + pendingOffsetS);
      seekPending.textContent = "Reloading\u2026";
      seekCancel.style.display = "none";
      var watchUrl;
      if (localFile) {
        watchUrl = "/local_watch?file=" + encodeURIComponent(localFile) + "&seek=" + targetSeek;
        if (syncMs && syncMs !== "0") watchUrl += "&sync=" + encodeURIComponent(syncMs);
      } else {
        watchUrl = "/watch?url=" + encodeURIComponent(videoUrl) + "&seek=" + targetSeek;
        if (videoQuality) watchUrl += "&quality=" + encodeURIComponent(videoQuality);
        if (syncMs && syncMs !== "0") watchUrl += "&sync=" + encodeURIComponent(syncMs);
      }
      window.location.href = watchUrl;
    }, SEEK_DEBOUNCE_MS);
  }

  if (videoUrl || localFile) {
    document.querySelectorAll(".seek-btn").forEach(function (btn) {
      btn.addEventListener("click", function () {
        pendingOffsetS = Math.max(-baseSeekS, pendingOffsetS + parseInt(btn.getAttribute("data-mins"), 10) * 60);
        startSeekTimer();
      });
    });

    seekCancel.addEventListener("click", function () {
      clearTimeout(seekTimer);
      clearInterval(countdownInterval);
      pendingOffsetS = 0;
      seekPending.textContent = "";
      seekCancel.style.display = "none";
    });
  } else {
    // Seek not available (e.g. direct stream)
    document.querySelector(".seek-bar").style.display = "none";
    elapsedEl.style.display = "none";
  }

  // Fetch fps + title from server once the stream is live
  var titleEl = document.getElementById("stream-title");
  (function pollStatus() {
    var xhr = new XMLHttpRequest();
    xhr.open("GET", "/stream_status?sid=" + encodeURIComponent(sid), true);
    xhr.timeout = 3000;
    xhr.onreadystatechange = function () {
      if (xhr.readyState !== 4) return;
      try {
        var d = JSON.parse(xhr.responseText);
        if (d.title && titleEl.textContent !== d.title) titleEl.textContent = d.title;
        if (!d.title) setTimeout(pollStatus, 2000);
      } catch(e) {
        setTimeout(pollStatus, 2000);
      }
    };
    xhr.send();
  })();

  // ── Elapsed time display ────────────────────────────────────────────────
  var pageStartMs = Date.now();

  function currentElapsedS() {
    return baseSeekS + Math.floor((Date.now() - pageStartMs) / 1000);
  }

  function fmtElapsed(s) {
    var h = Math.floor(s / 3600);
    var m = Math.floor((s % 3600) / 60);
    var sec = s % 60;
    return h + ":" + (m < 10 ? "0" : "") + m + ":" + (sec < 10 ? "0" : "") + sec;
  }

  if (videoUrl || localFile) {
    setInterval(function () {
      elapsedEl.textContent = fmtElapsed(currentElapsedS());
    }, 1000);
  }

  // ── Progress save / resume ──────────────────────────────────────────────
  var progressKey = videoUrl || localFile;

  function buildResumeUrl(posS) {
    if (localFile) {
      var u = "/local_watch?file=" + encodeURIComponent(localFile) + "&seek=" + posS;
      if (syncMs && syncMs !== "0") u += "&sync=" + encodeURIComponent(syncMs);
      return u;
    }
    var u = "/watch?url=" + encodeURIComponent(videoUrl) + "&seek=" + posS;
    if (videoQuality) u += "&quality=" + encodeURIComponent(videoQuality);
    if (syncMs && syncMs !== "0") u += "&sync=" + encodeURIComponent(syncMs);
    return u;
  }

  function saveProgress(posS) {
    if (!progressKey || posS < 10) return;
    var xhr = new XMLHttpRequest();
    xhr.open("POST", "/progress", true);
    xhr.setRequestHeader("Content-Type", "application/json");
    xhr.send(JSON.stringify({url: progressKey, pos_s: posS}));
  }

  function clearProgress() {
    if (!progressKey) return;
    var xhr = new XMLHttpRequest();
    xhr.open("DELETE", "/progress?url=" + encodeURIComponent(progressKey), true);
    xhr.send();
  }

  // Save every 30 seconds
  if (progressKey) {
    setInterval(function () { saveProgress(currentElapsedS()); }, 30000);
  }

  // Check for saved position on load — offer resume if > 60s into the video
  // and we're not already starting from a seek position
  if (progressKey && baseSeekS === 0) {
    var chkXhr = new XMLHttpRequest();
    chkXhr.open("GET", "/progress?url=" + encodeURIComponent(progressKey), true);
    chkXhr.timeout = 3000;
    chkXhr.onreadystatechange = function () {
      if (chkXhr.readyState !== 4) return;
      try {
        var saved = JSON.parse(chkXhr.responseText);
        var posS = saved.pos_s || 0;
        var savedAt = saved.saved_at || 0;
        var ageH = (Date.now() / 1000 - savedAt) / 3600;
        // Only offer resume if position is > 1 min and saved within 48 h
        if (posS > 60 && ageH < 48) {
          resumeText.textContent = "Resume from " + fmtElapsed(posS) + "?";
          resumeYes.href = buildResumeUrl(posS);
          resumeYes.addEventListener("click", function () { clearProgress(); });
          resumeBanner.style.display = "flex";
        }
      } catch(e) {}
    };
    chkXhr.send();
  }

  resumeNo.addEventListener("click", function () {
    resumeBanner.style.display = "none";
  });

  // On stream error, add position hint to the diagnostics message
  var origError = img.onerror;
  img.addEventListener("error", function () {
    var posS = currentElapsedS();
    if (posS > 10) {
      saveProgress(posS);
      // Append resume link below the existing diag after a short delay
      // (let the existing error handler run first)
      setTimeout(function () {
        if (diag.style.display !== "none" && progressKey) {
          diag.textContent += "\\n\\nLast saved position: " + fmtElapsed(posS) +
            "\\nReload from here: " + window.location.origin + buildResumeUrl(posS);
        }
      }, 500);
    }
  });
})();
</script>
</body></html>"""


AUDIO_WATCH_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>OpenCarStream — Audio</title>
<style>
  @import url('https://fonts.googleapis.com/css2?family=Orbitron:wght@700;900&family=Rajdhani:wght@300;500&display=swap');
  :root{--red:#e31937;--dark:#090909;--panel:#111117;--border:#252530;--text:#e0e0ee;--muted:#555568;}
  @media(prefers-color-scheme:light){:root{--dark:#f4f4f6;--panel:#ffffff;--border:#d8d8e0;--text:#1a1a2e;--muted:#888899;}}
  *{margin:0;padding:0;box-sizing:border-box;}
  body{background:var(--dark);color:var(--text);font-family:'Rajdhani',sans-serif;min-height:100vh;display:flex;flex-direction:column;align-items:center;padding:16px;}
  .top{width:100%;max-width:720px;display:flex;justify-content:space-between;align-items:center;margin-bottom:20px;gap:12px;}
  .title{font-family:'Orbitron',monospace;letter-spacing:.1em;color:var(--red);font-size:1rem;}
  .back{color:var(--red);text-decoration:none;font-family:monospace;}
  .wrap{width:100%;max-width:720px;background:var(--panel);border:1px solid var(--border);border-radius:12px;padding:28px 24px;display:flex;flex-direction:column;gap:14px;}
  audio{width:100%;}
  .stream-title{font-size:1rem;color:var(--text);font-family:'Rajdhani',sans-serif;font-weight:500;letter-spacing:.02em;min-height:1.4em;}
  .diag{padding:10px 12px;border:1px solid var(--border);border-radius:8px;font-family:monospace;font-size:.85rem;line-height:1.4;white-space:pre-wrap;color:#f0b5bf;background:#160d11;display:none;}
  .status{font-family:'Orbitron',monospace;font-size:.7rem;letter-spacing:.1em;color:var(--red);text-transform:uppercase;}
  .seek-bar{display:flex;align-items:center;gap:8px;flex-wrap:wrap;padding-top:10px;border-top:1px solid var(--border);}
  .seek-btn{background:var(--panel);border:1px solid var(--border);color:var(--text);font-family:'Rajdhani',sans-serif;font-size:.95rem;font-weight:500;padding:6px 12px;border-radius:6px;cursor:pointer;}
  .seek-btn:hover{border-color:var(--red);color:var(--red);}
  .elapsed{font-family:monospace;font-size:1rem;color:var(--text);margin-left:auto;letter-spacing:.05em;}
  .live-badge{font-family:'Orbitron',monospace;font-size:.65rem;letter-spacing:.12em;color:#fff;background:var(--red);padding:2px 7px;border-radius:3px;margin-left:auto;display:none;}
  .seek-label{font-family:'Orbitron',monospace;font-size:.65rem;letter-spacing:.1em;color:var(--muted);text-transform:uppercase;}
  .seek-pending{font-family:monospace;font-size:.85rem;color:var(--red);}
  .seek-cancel{background:none;border:none;color:#888;font-size:.8rem;cursor:pointer;text-decoration:underline;padding:0;}
</style>
</head>
<body>
  <div class="top">
    <div class="title">AUDIO STREAM</div>
    <a class="back" href="/">← Back</a>
  </div>
  <div class="wrap">
    <div id="stream-title" class="stream-title"></div>
    <div id="status-msg" class="status">Connecting…</div>
    <audio id="audio" controls autoplay playsinline></audio>
    <div class="seek-bar" id="seek-bar">
      <span class="seek-label">Seek</span>
      <button class="seek-btn" data-mins="-10">-10 min</button>
      <button class="seek-btn" data-mins="1">+1 min</button>
      <button class="seek-btn" data-mins="5">+5 min</button>
      <button class="seek-btn" data-mins="10">+10 min</button>
      <span id="seek-pending" class="seek-pending"></span>
      <button id="seek-cancel" class="seek-cancel" style="display:none">cancel</button>
      <span id="live-badge" class="live-badge">● Live</span>
      <span id="elapsed" class="elapsed">0:00:00</span>
    </div>
    <div id="diag" class="diag"></div>
  </div>
<script>
(function () {
  var sid        = "{{stream_id}}";
  var syncMs     = "{{sync_ms}}";
  var videoUrl   = "{{video_url}}";
  var seekS      = parseInt("{{seek_s}}", 10) || 0;
  var durationS  = parseInt("{{duration_s}}", 10) || 0;  // 0 = unknown/live
  if (!sid) { window.location.href = "/"; return; }

  var audio      = document.getElementById("audio");
  var titleEl    = document.getElementById("stream-title");
  var statusEl   = document.getElementById("status-msg");
  var diagEl     = document.getElementById("diag");
  var elapsedEl  = document.getElementById("elapsed");
  var liveBadge  = document.getElementById("live-badge");
  var seekBar    = document.getElementById("seek-bar");
  var seekPend   = document.getElementById("seek-pending");
  var seekCancel = document.getElementById("seek-cancel");

  audio.src = "/audio?sid=" + encodeURIComponent(sid) + "&sync=" + encodeURIComponent(syncMs);
  audio.preload = "auto";
  try { var p = audio.play(); if (p && p.catch) p.catch(function(){}); } catch(e) {}

  var retryPlay = function () {
    try { var p2 = audio.play(); if (p2 && p2.catch) p2.catch(function(){}); } catch(e) {}
    window.removeEventListener("click", retryPlay, true);
    window.removeEventListener("touchstart", retryPlay, true);
  };
  window.addEventListener("click", retryPlay, true);
  window.addEventListener("touchstart", retryPlay, true);

  audio.addEventListener("playing", function () { statusEl.textContent = "Playing"; });
  audio.addEventListener("waiting", function () { statusEl.textContent = "Buffering…"; });
  audio.addEventListener("loadedmetadata", function () {
    // audio.duration is always Infinity for piped MP3 streams; use durationS
    // (fetched via yt-dlp) to distinguish live streams from VODs.
    var isLiveStream = !isFinite(audio.duration) && durationS === 0;
    if (isLiveStream) {
      liveBadge.style.display = "inline-block";
      elapsedEl.style.display = "none";
      seekBar.style.display   = videoUrl ? "" : "none";  // hide seek for live without url
    }
  });
  audio.addEventListener("error", function () {
    statusEl.textContent = "Error loading audio";
    var xhr = new XMLHttpRequest();
    xhr.open("GET", "/stream_status?sid=" + encodeURIComponent(sid), true);
    xhr.onreadystatechange = function () {
      if (xhr.readyState !== 4) return;
      try {
        var d = JSON.parse(xhr.responseText);
        diagEl.style.display = "block";
        diagEl.textContent = "status: " + d.status + "\\nerror: " + (d.error || "n/a") + "\\ndetail: " + (d.error_detail || "n/a");
      } catch(e) {}
    };
    xhr.send();
  });

  // ── Elapsed time ─────────────────────────────────────────────────────────
  var pageStartMs = Date.now();
  function currentElapsedS() { return seekS + Math.floor((Date.now() - pageStartMs) / 1000); }
  function fmtTime(s) {
    var h = Math.floor(s / 3600), m = Math.floor((s % 3600) / 60), sec = s % 60;
    return h + ":" + (m < 10 ? "0" : "") + m + ":" + (sec < 10 ? "0" : "") + sec;
  }
  setInterval(function () { elapsedEl.textContent = fmtTime(currentElapsedS()); }, 1000);

  // ── Seek controls (VOD only) ──────────────────────────────────────────────
  var pendingOffsetS = 0;
  var seekTimer = null, countdownInterval = null;
  var SEEK_DEBOUNCE_MS = 3000;

  if (videoUrl) {
    document.querySelectorAll(".seek-btn").forEach(function (btn) {
      btn.addEventListener("click", function () {
        pendingOffsetS = Math.max(-seekS, pendingOffsetS + parseInt(btn.getAttribute("data-mins"), 10) * 60);
        startSeekTimer();
      });
    });
    seekCancel.addEventListener("click", function () {
      clearTimeout(seekTimer); clearInterval(countdownInterval);
      pendingOffsetS = 0; seekPend.textContent = ""; seekCancel.style.display = "none";
    });
  } else {
    seekBar.style.display = "none";
  }

  function startSeekTimer() {
    clearTimeout(seekTimer); clearInterval(countdownInterval);
    var countdown = SEEK_DEBOUNCE_MS / 1000;
    var sign = pendingOffsetS >= 0 ? "+" : "";
    seekPend.textContent = sign + Math.floor(pendingOffsetS / 60) + "m (seeking in " + countdown + "s)";
    seekCancel.style.display = "inline";
    countdownInterval = setInterval(function () {
      countdown--;
      if (countdown > 0) {
        var s2 = pendingOffsetS >= 0 ? "+" : "";
        seekPend.textContent = s2 + Math.floor(pendingOffsetS / 60) + "m (seeking in " + countdown + "s)";
      }
    }, 1000);
    seekTimer = setTimeout(function () {
      clearInterval(countdownInterval);
      var target = Math.max(0, seekS + pendingOffsetS);
      window.location.href = "/watch?url=" + encodeURIComponent(videoUrl) +
        "&mode=audio&seek=" + target +
        (syncMs && syncMs !== "0" ? "&sync=" + encodeURIComponent(syncMs) : "");
    }, SEEK_DEBOUNCE_MS);
  }

  // ── Title poll ────────────────────────────────────────────────────────────
  (function pollTitle() {
    var xhr = new XMLHttpRequest();
    xhr.open("GET", "/stream_status?sid=" + encodeURIComponent(sid), true);
    xhr.timeout = 3000;
    xhr.onreadystatechange = function () {
      if (xhr.readyState !== 4) return;
      try {
        var d = JSON.parse(xhr.responseText);
        if (d.title) titleEl.textContent = d.title;
        if (!d.title) setTimeout(pollTitle, 2000);
      } catch(e) { setTimeout(pollTitle, 2000); }
    };
    xhr.send();
  })();
})();
</script>
</body></html>"""


MP4_WATCH_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>OpenCarStream — MP4</title>
<style>
  @import url('https://fonts.googleapis.com/css2?family=Orbitron:wght@700;900&family=Rajdhani:wght@300;500&display=swap');
  :root{--red:#e31937;--dark:#090909;--panel:#111117;--border:#252530;--text:#e0e0ee;}
  @media(prefers-color-scheme:light){:root{--dark:#f4f4f6;--panel:#ffffff;--border:#d8d8e0;--text:#1a1a2e;}}
  *{margin:0;padding:0;box-sizing:border-box;}
  body{background:var(--dark);color:var(--text);font-family:'Rajdhani',sans-serif;min-height:100vh;display:flex;flex-direction:column;align-items:center;padding:16px;}
  .top{width:100%;max-width:1280px;display:flex;justify-content:space-between;align-items:center;margin-bottom:10px;gap:12px;}
  .title{font-family:'Orbitron',monospace;letter-spacing:.1em;color:var(--red);font-size:1rem;}
  .back{color:var(--red);text-decoration:none;font-family:monospace;}
  .wrap{width:100%;max-width:1280px;background:var(--panel);border:1px solid var(--border);border-radius:10px;padding:10px;}
  video{width:100%;height:auto;display:block;background:black;border-radius:8px;}
  .stream-title{font-size:.95rem;color:var(--text);font-family:'Rajdhani',sans-serif;font-weight:500;padding:8px 4px 2px;letter-spacing:.02em;min-height:1.4em;}
  .err{margin-top:10px;padding:12px 16px;background:#160d11;border:1px solid var(--red);border-radius:8px;font-family:monospace;font-size:.9rem;color:#f0b5bf;display:none;}
</style>
</head>
<body>
  <div class="top">
    <div class="title">MP4 STREAM</div>
    <a class="back" href="/">← Back</a>
  </div>
  <div class="wrap">
    <video id="video" controls autoplay playsinline>
      <source src="{{direct_url}}" type="video/mp4">
      Your browser does not support HTML5 video.
    </video>
    <div id="stream-title" class="stream-title">{{stream_title}}</div>
    <div id="err" class="err">{{error_msg}}</div>
  </div>
<script>
(function () {
  var vid = document.getElementById("video");
  var errEl = document.getElementById("err");
  var errMsg = "{{error_msg}}";
  if (errMsg) { errEl.style.display = "block"; vid.style.display = "none"; return; }
  vid.addEventListener("error", function () {
    errEl.style.display = "block";
    errEl.textContent = "Video failed to load. The direct URL may have expired — go back and try again.";
  });
  try { var p = vid.play(); if (p && p.catch) p.catch(function(){}); } catch(e) {}
})();
</script>
</body></html>"""


def render_status_page() -> str:
    streams = registry.all_streams()
    if not streams:
        streams_html = '<p class="empty">No active streams</p>'
    else:
        rows = []
        for s in sorted(streams, key=lambda x: x.created_at, reverse=True):
            title = (s.title or s.url[:60] + "…").replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
            stream_url = f"/watch?url={quote(s.url, safe='')}"
            quality_tag = ""
            if s.quality:
                stream_url += f"&quality={s.quality}"
                quality_tag = f" · {s.quality}p"
            rows.append(
                f'<div class="stream-row">'
                f'<div><a href="{stream_url}">{title}{quality_tag}</a></div>'
                f'<div style="display:flex;align-items:center;gap:10px;">'
                f'<span class="badge {s.status}">{s.status.upper()}</span>'
                f'<button onclick="stopStream(\'{s.id}\')" title="Stop stream" '
                f'style="background:none;border:none;color:var(--muted);font-size:1.1rem;cursor:pointer;padding:0;line-height:1;" '
                f'onmouseover="this.style.color=\'var(--red)\'" onmouseout="this.style.color=\'var(--muted)\'">✕</button>'
                f'</div>'
                f'</div>'
            )
        streams_html = "\n".join(rows)

    subs_status = "loaded" if os.path.isfile(SUBSCRIPTIONS_FILE) else "not mounted"
    iptv_status = "mounted" if os.path.isdir(IPTV_LISTS_DIR) else "not mounted"
    return (STATUS_HTML
            .replace("{{stream_count}}", str(len(streams)))
            .replace("{{streams_html}}", streams_html)
            .replace("{{fps}}", str(MJPEG_FPS))
            .replace("{{quality}}", str(FFMPEG_QUALITY))
            .replace("{{width}}", str(STREAM_WIDTH))
            .replace("{{height}}", str(STREAM_HEIGHT))
            .replace("{{max_streams}}", str(MAX_STREAMS))
            .replace("{{audio_delay_ms}}", str(AUDIO_DELAY_MS))
            .replace("{{local_media_video_delay_ms}}", str(LOCAL_MEDIA_VIDEO_DELAY_MS))
            .replace("{{subs_status}}", subs_status)
            .replace("{{iptv_status}}", iptv_status)
            .replace("{{pluto_langs}}", ", ".join(PLUTO_LANGS))
            .replace("{{pluto_langs_json}}", json.dumps(PLUTO_LANGS))
            .replace("{{local_media_dir}}", LOCAL_MEDIA_DIR))

def render_watch_page(stream_id: str, sync_ms: int, video_url: str = "", quality: int | None = None,
                      local_file: str = "", seek_s: int = 0) -> str:
    return (WATCH_HTML
            .replace("{{stream_id}}", stream_id)
            .replace("{{sync_ms}}", str(sync_ms))
            .replace("{{video_url}}", video_url)
            .replace("{{video_quality}}", str(quality or ""))
            .replace("{{local_file}}", local_file)
            .replace("{{seek_s}}", str(seek_s)))

def render_audio_page(stream_id: str, sync_ms: int, video_url: str = "", seek_s: int = 0, duration_s: int = 0) -> str:
    return (AUDIO_WATCH_HTML
            .replace("{{stream_id}}", stream_id)
            .replace("{{sync_ms}}", str(sync_ms))
            .replace("{{video_url}}", video_url)
            .replace("{{seek_s}}", str(seek_s))
            .replace("{{duration_s}}", str(duration_s)))

def render_mp4_page(direct_url: str, error_msg: str = "", stream_title: str = "") -> str:
    return (MP4_WATCH_HTML
            .replace("{{direct_url}}", direct_url)
            .replace("{{stream_title}}", stream_title)
            .replace("{{error_msg}}", error_msg))


# ── HTTP handler ──────────────────────────────────────────────────────────────
class Handler(BaseHTTPRequestHandler):
    disable_nagle_algorithm = True  # TCP_NODELAY — eliminates inter-frame buffering delay

    def log_message(self, fmt, *args):
        log.debug(fmt % args)

    @staticmethod
    def _safe_header_value(value: str) -> str:
        # http.server writes headers as latin-1; replace unsupported chars so
        # titles with unicode punctuation/emojis do not crash the request.
        cleaned = (value or "").replace("\r", " ").replace("\n", " ")
        return cleaned.encode("latin-1", "replace").decode("latin-1")

    @staticmethod
    def _parse_quality(raw_quality: str | None) -> int | None:
        if raw_quality is None or raw_quality == "":
            return None
        try:
            quality = int(raw_quality)
        except ValueError:
            raise ValueError("quality must be one of: 144,240,360,480,720,1080")
        if quality not in {144, 240, 360, 480, 720, 1080}:
            raise ValueError("quality must be one of: 144,240,360,480,720,1080")
        return quality

    @staticmethod
    def _parse_sync_ms(raw_sync: str | None, default_ms: int | None = None) -> int:
        if raw_sync is None or raw_sync == "":
            return AUDIO_DELAY_MS if default_ms is None else default_ms
        try:
            sync_ms = int(raw_sync)
        except ValueError:
            raise ValueError("sync must be an integer milliseconds value")
        if sync_ms < 0 or sync_ms > 10000:
            raise ValueError("sync must be between 0 and 10000 milliseconds")
        return sync_ms

    @staticmethod
    def _resolve_local_media_path(rel_path: str | None) -> tuple[str | None, str]:
        if not rel_path:
            return None, "Missing ?file= parameter"
        # Keep path traversal protections (`..`) while allowing symlink targets
        # outside the base directory when they are reachable via entries inside
        # the mounted media tree.
        base = os.path.abspath(LOCAL_MEDIA_DIR)
        target = os.path.abspath(os.path.normpath(os.path.join(base, rel_path)))
        if not (target == base or target.startswith(base + os.sep)):
            return None, "Invalid local media path"
        if not os.path.isfile(target):
            return None, "Local media file not found"
        if not _has_supported_media_ext(target):
            return None, "Unsupported local media extension"
        return target, ""

    @staticmethod
    def _resolve_iptv_list_path(raw_list: str | None) -> tuple[str | None, str]:
        if not raw_list:
            return None, "Missing ?list= parameter"

        requested = raw_list.strip()
        if not requested:
            return None, "Missing ?list= parameter"

        base, lists, err = _scan_iptv_lists()
        if err:
            return None, err

        request_lower = requested.lower()
        for entry in lists:
            if entry["id"].lower() == request_lower:
                return os.path.join(base, entry["id"].replace("/", os.sep)), ""

        # Allow resolving by friendly name (filename without extension).
        by_name = [entry for entry in lists if entry["name"].lower() == request_lower]
        if len(by_name) == 1:
            return os.path.join(base, by_name[0]["id"].replace("/", os.sep)), ""
        if len(by_name) > 1:
            return None, (
                f"Ambiguous IPTV list name '{requested}'. "
                "Use the full list id/path from /iptv_lists."
            )

        return None, f"IPTV list not found: {requested}"

    def do_GET(self):
        parsed = urlparse(self.path)
        qs     = parse_qs(parsed.query)
        path   = parsed.path.rstrip("/") or "/"

        if path == "/":
            html = render_status_page()
            self._html(html)

        elif path == "/health":
            self._json({"ok": True, "streams": len(registry.all_streams())})

        elif path == "/status":
            data = [s.to_dict() for s in registry.all_streams()]
            self._json({"streams": data})

        elif path == "/feed":
            channel = qs.get("channel", [None])[0]
            if not channel:
                self._error(400, "Missing ?channel= parameter")
                return
            limit = 12
            try:
                raw_limit = qs.get("limit", [None])[0]
                if raw_limit:
                    limit = max(1, min(int(raw_limit), 50))
            except (ValueError, TypeError):
                pass
            self._serve_feed(channel.strip(), limit)

        elif path == "/ytsearch":
            q = qs.get("q", [None])[0]
            if not q:
                self._error(400, "Missing ?q= parameter")
                return
            limit = 12
            try:
                raw_limit = qs.get("limit", [None])[0]
                if raw_limit:
                    limit = max(1, min(int(raw_limit), 50))
            except (ValueError, TypeError):
                pass
            self._serve_ytsearch(q.strip(), limit)

        elif path == "/subscriptions":
            self._serve_subscriptions()

        elif path == "/iptv_lists":
            self._serve_iptv_lists()

        elif path == "/iptv_streams":
            list_name = qs.get("list", [None])[0]
            self._serve_iptv_streams(list_name)

        elif path == "/stream_fmp4":
            raw_url = qs.get("url", [None])[0]
            if not raw_url:
                self._error(400, "Missing ?url= parameter")
                return
            stream_url = unquote(raw_url)
            self._serve_fmp4_direct(stream_url)

        elif path == "/file_serve":
            raw_path = qs.get("path", [None])[0]
            if not raw_path:
                self._error(400, "Missing ?path= parameter")
                return
            req_path = unquote(raw_path)
            local_file, err = self._resolve_local_media_path(
                os.path.relpath(req_path, os.path.abspath(LOCAL_MEDIA_DIR))
            )
            if not local_file:
                self._error(400, err)
                return
            self._serve_file_bytes(local_file)

        elif path == "/local_media":
            raw_dir = qs.get("dir", [None])[0]
            self._serve_local_media(raw_dir)

        elif path == "/local_watch":
            raw_file = qs.get("file", [None])[0]
            raw_sync = qs.get("sync", [None])[0]
            raw_seek = qs.get("seek", [None])[0]
            if raw_sync is None or raw_sync == "":
                sync_ms = LOCAL_MEDIA_VIDEO_DELAY_MS
            else:
                try:
                    sync_ms = self._parse_sync_ms(raw_sync)
                except ValueError as e:
                    self._error(400, str(e))
                    return
            seek_s = 0
            if raw_seek:
                try:
                    seek_s = max(0, int(raw_seek))
                except ValueError:
                    pass
            local_file, err = self._resolve_local_media_path(raw_file)
            if not local_file:
                self._error(400, err)
                return
            file_url = "file://" + quote(local_file, safe="/")
            registry.cleanup_done()
            stream = registry.get_or_create(
                file_url,
                quality=None,
                reuse_existing=False,
            )
            if not stream.title:
                stream.title = os.path.splitext(os.path.basename(local_file))[0]
            if seek_s > 0:
                stream.seek_s = float(seek_s)
            local_mode = (qs.get("mode", ["mjpeg"])[0] or "mjpeg").lower()
            if local_mode not in ("mjpeg", "mp4", "audio"):
                local_mode = "mjpeg"

            if local_mode == "mp4":
                vcodec, acodec = _probe_local_codecs(local_file)
                fname = os.path.basename(local_file)
                # Browsers support H.264/H.265 video and AAC/MP3 audio natively in MP4
                video_ok = vcodec in ("h264", "hevc")
                audio_ok = acodec in ("aac", "mp3", "")
                if video_ok and audio_ok:
                    log.info(f"MP4 {fname}: video:{vcodec}→copy, audio:{acodec or 'none'}→copy (direct)")
                    mp4_url = "/file_serve?path=" + quote(local_file, safe="")
                else:
                    vlog = f"video:{vcodec or '?'}→{'copy' if video_ok else 'h264'}"
                    alog = f"audio:{acodec or '?'}→{'copy' if audio_ok else 'aac'}"
                    log.info(f"MP4 {fname}: {vlog}, {alog} (transcoding)")
                    mp4_url = "/stream_fmp4?url=" + quote(file_url, safe="")
                self._html(render_mp4_page(mp4_url))
                return

            if local_mode == "audio":
                stream.audio_only = True
                self._html(render_audio_page(stream.id, sync_ms))
                return

            # Warm local playback so configured sync delay reflects timeline
            # delay rather than ffmpeg startup overhead.
            if stream.status == "starting" and stream._ff_proc is None:
                threading.Thread(target=run_pipeline, args=(stream,), daemon=True).start()
            warm_deadline = time.time() + 8.0
            while (
                stream.frame is None
                and stream.status not in ("error", "done")
                and time.time() < warm_deadline
            ):
                time.sleep(0.05)
            self._html(render_watch_page(stream.id, sync_ms, local_file=raw_file or "", seek_s=seek_s))

        elif path == "/pluto_channels":
            lang = qs.get("lang", [PLUTO_LANGS[0]])[0]
            self._serve_pluto_channels(lang)

        elif path == "/pluto_watch":
            lang = (qs.get("lang", [PLUTO_LANGS[0]])[0] or "").strip().lower()
            channel_id = qs.get("id", [None])[0]
            if not channel_id:
                self._error(400, "Missing ?id= parameter")
                return
            raw_sync = qs.get("sync", [None])[0]
            try:
                sync_ms = self._parse_sync_ms(raw_sync, 500)
            except ValueError as e:
                self._error(400, str(e))
                return
            if lang not in PLUTO_LANGS:
                self._error(400, f"Unsupported Pluto lang '{lang}'")
                return

            # Refresh Pluto session tokens per playback launch to avoid stale
            # signed URLs being rejected with fallback "unsupported device" streams.
            pluto_url, err = pluto_cache.build_channel_url(
                lang, channel_id, force_refresh=True
            )
            if not pluto_url:
                self._error(502, f"Pluto TV stream unavailable: {err}")
                return
            registry.cleanup_done()
            stream = registry.get_or_create(
                pluto_url,
                quality=None,
                reuse_existing=False,
            )
            if not stream.title:
                with pluto_cache._lock:
                    ch = next((c for c in pluto_cache._by_lang.get(lang, []) if c.get("id") == channel_id), None)
                if ch:
                    stream.title = ch["name"]
            pluto_mode = (qs.get("mode", ["mjpeg"])[0] or "mjpeg").lower()
            if pluto_mode not in ("mjpeg", "mp4", "audio"):
                pluto_mode = "mjpeg"
            if pluto_mode == "mp4":
                direct_url, err = _resolve_mp4_url(pluto_url, None)
                self._html(render_mp4_page(direct_url, error_msg=err, stream_title=stream.title))
            elif pluto_mode == "audio":
                stream.audio_only = True
                self._html(render_audio_page(stream.id, sync_ms))
            else:
                self._html(render_watch_page(stream.id, sync_ms))

        elif path == "/stop_stream":
            sid = qs.get("sid", [None])[0]
            if not sid:
                self._error(400, "Missing ?sid= parameter")
                return
            stream = registry.get(sid)
            if stream:
                stream.stop()
                stream.status = "done"
            self._json({"ok": True})

        elif path == "/stream_status":
            sid = qs.get("sid", [None])[0]
            if not sid:
                self._error(400, "Missing ?sid= parameter")
                return
            stream = registry.get(sid)
            if stream is None:
                self._error(404, "Stream session not found")
                return
            self._json(stream.to_dict())

        elif path == "/watch":
            raw_url = qs.get("url", [None])[0]
            if not raw_url:
                self._error(400, "Missing ?url= parameter")
                return
            raw_quality = qs.get("quality", [None])[0]
            try:
                quality = self._parse_quality(raw_quality)
            except ValueError as e:
                self._error(400, str(e))
                return
            raw_sync = qs.get("sync", [None])[0]
            video_url = unquote(raw_url)
            try:
                sync_ms = self._parse_sync_ms(raw_sync, _default_sync_ms_for_url(video_url))
            except ValueError as e:
                self._error(400, str(e))
                return
            mode = (qs.get("mode", ["mjpeg"])[0] or "mjpeg").lower()
            if mode not in ("mjpeg", "mp4", "audio"):
                mode = "mjpeg"

            if mode == "mp4":
                direct_url, err = _resolve_mp4_url(video_url, quality)
                self._html(render_mp4_page(direct_url, error_msg=err))
                return

            try:
                seek_s = max(0.0, float(qs.get("seek", [0])[0] or 0))
            except (ValueError, TypeError):
                seek_s = 0.0
            registry.cleanup_done()
            stream = registry.get_or_create(
                video_url,
                quality=quality,
                reuse_existing=False,
            )
            stream.seek_s = seek_s
            if mode == "audio":
                stream.audio_only = True
                duration_s = _fetch_duration_s(video_url)
                self._html(render_audio_page(stream.id, sync_ms, video_url, int(seek_s), duration_s))
            else:
                self._html(render_watch_page(stream.id, sync_ms, video_url, quality))

        elif path == "/stream":
            raw_sync = qs.get("sync", [None])[0]
            try:
                sync_ms = self._parse_sync_ms(raw_sync)
            except ValueError as e:
                self._error(400, str(e))
                return
            sid = qs.get("sid", [None])[0]
            stream = None
            if sid:
                stream = registry.get(sid)
                if stream is None:
                    self._error(404, "Stream session not found")
                    return
            else:
                raw_url = qs.get("url", [None])[0]
                if not raw_url:
                    self._error(400, "Missing ?url= parameter")
                    return
                raw_quality = qs.get("quality", [None])[0]
                try:
                    quality = self._parse_quality(raw_quality)
                except ValueError as e:
                    self._error(400, str(e))
                    return
                video_url = unquote(raw_url)
                stream = registry.get_or_create(video_url, quality=quality)
            self._serve_mjpeg(stream, sync_ms=sync_ms)

        elif path == "/audio":
            raw_sync = qs.get("sync", [None])[0]
            try:
                sync_ms = self._parse_sync_ms(raw_sync)
            except ValueError as e:
                self._error(400, str(e))
                return
            sid = qs.get("sid", [None])[0]
            stream = None
            if sid:
                stream = registry.get(sid)
                if stream is None:
                    self._error(404, "Stream session not found")
                    return
            else:
                raw_url = qs.get("url", [None])[0]
                if not raw_url:
                    self._error(400, "Missing ?url= parameter")
                    return
                raw_quality = qs.get("quality", [None])[0]
                try:
                    quality = self._parse_quality(raw_quality)
                except ValueError as e:
                    self._error(400, str(e))
                    return
                video_url = unquote(raw_url)
                stream = registry.get_or_create(video_url, quality=quality)
            self._serve_audio(stream, sync_ms=sync_ms)

        elif path == "/ace_streams":
            self._serve_ace_streams()

        elif path == "/favorites":
            self._json({"favorites": _load_favorites()})

        elif path == "/progress":
            url = (qs.get("url", [None])[0] or "").strip()
            data = _load_progress()
            if url:
                self._json(data.get(url) or {})
            else:
                self._json(data)

        elif path == "/subscriptions_feed":
            force = qs.get("force", [None])[0] == "1"
            self._serve_subscriptions_feed(force)

        else:
            self._error(404, "Not found")

    def do_POST(self):
        parsed = urlparse(self.path)
        path   = parsed.path.rstrip("/") or "/"

        if path == "/ace_streams":
            length = int(self.headers.get("Content-Length", 0))
            body   = self.rfile.read(length)
            try:
                item = json.loads(body)
            except Exception:
                self._error(400, "Invalid JSON")
                return
            name = (item.get("name") or "").strip()
            cid  = (item.get("id")   or "").strip()
            if not name or not cid:
                self._error(400, "Missing name or id")
                return
            streams = _load_ace_streams()
            streams.append({"name": name, "id": cid})
            _save_ace_streams(streams)
            self._json({"ok": True, "streams": streams})

        elif path == "/favorites":
            length = int(self.headers.get("Content-Length", 0))
            body   = self.rfile.read(length)
            try:
                item = json.loads(body)
            except Exception:
                self._error(400, "Invalid JSON")
                return
            url = (item.get("url") or "").strip()
            if not url:
                self._error(400, "Missing url")
                return
            favs = _load_favorites()
            if url not in favs:
                favs.append(url)
                _save_favorites(favs)
            self._json({"ok": True, "favorites": favs})

        elif path == "/progress":
            length = int(self.headers.get("Content-Length", 0))
            body   = self.rfile.read(length)
            try:
                item = json.loads(body)
            except Exception:
                self._error(400, "Invalid JSON")
                return
            url   = (item.get("url") or "").strip()
            pos_s = item.get("pos_s")
            if not url or pos_s is None:
                self._error(400, "Missing url or pos_s")
                return
            data = _load_progress()
            data[url] = {"pos_s": int(pos_s), "saved_at": int(time.time())}
            _save_progress(data)
            self._json({"ok": True})

        else:
            self._error(404, "Not found")

    def do_DELETE(self):
        parsed = urlparse(self.path)
        path   = parsed.path.rstrip("/") or "/"

        if path == "/ace_streams":
            qs  = parse_qs(parsed.query)
            idx_raw = qs.get("idx", [None])[0]
            try:
                idx = int(idx_raw)
            except (TypeError, ValueError):
                self._error(400, "Missing or invalid ?idx= parameter")
                return
            streams = _load_ace_streams()
            if idx < 0 or idx >= len(streams):
                self._error(404, "Index out of range")
                return
            streams.pop(idx)
            _save_ace_streams(streams)
            self._json({"ok": True, "streams": streams})

        elif path == "/favorites":
            qs  = parse_qs(parsed.query)
            url = (qs.get("url", [None])[0] or "").strip()
            if not url:
                self._error(400, "Missing ?url= parameter")
                return
            favs = _load_favorites()
            favs = [f for f in favs if f != url]
            _save_favorites(favs)
            self._json({"ok": True, "favorites": favs})

        elif path == "/progress":
            qs  = parse_qs(parsed.query)
            url = (qs.get("url", [None])[0] or "").strip()
            if not url:
                self._error(400, "Missing ?url= parameter")
                return
            data = _load_progress()
            data.pop(url, None)
            _save_progress(data)
            self._json({"ok": True})

        else:
            self._error(404, "Not found")

    # ── Ace streams ───────────────────────────────────────────────────────────
    def _serve_ace_streams(self):
        self._json({"streams": _load_ace_streams()})

    # ── Subscriptions ─────────────────────────────────────────────────────────
    def _serve_subscriptions(self):
        if not os.path.isfile(SUBSCRIPTIONS_FILE):
            self._error(503, f"Subscriptions file not found at {SUBSCRIPTIONS_FILE}. "
                            "Run sync_subscriptions.py and mount the resulting JSON.")
            return
        try:
            with open(SUBSCRIPTIONS_FILE, encoding="utf-8") as f:
                data = json.load(f)
        except Exception as e:
            self._error(500, f"Failed to read subscriptions file: {e}")
            return
        self._json({
            "synced_at": data.get("synced_at", ""),
            "channels":  data.get("channels", []),
        })

    def _serve_subscriptions_feed(self, force: bool = False):
        if not os.path.isfile(SUBSCRIPTIONS_FILE):
            self._error(503, "Subscriptions file not found")
            return
        try:
            with open(SUBSCRIPTIONS_FILE, encoding="utf-8") as f:
                data = json.load(f)
        except Exception as e:
            self._error(500, f"Failed to read subscriptions file: {e}")
            return

        channels = data.get("channels", [])
        if not channels:
            self._json({"videos": [], "built_at": 0, "cached": False})
            return

        with _home_feed_lock:
            age = time.time() - _home_feed_cache["built_at"]
            if not force and HOME_FEED_CACHE_SECS > 0 and age < HOME_FEED_CACHE_SECS and _home_feed_cache["videos"]:
                self._json({
                    "videos":   _home_feed_cache["videos"],
                    "built_at": int(_home_feed_cache["built_at"]),
                    "cached":   True,
                })
                return

        log.info(f"Building home feed from {len(channels)} channels ({HOME_FEED_WORKERS} workers)…")
        t0 = time.time()
        videos = _build_home_feed(channels)

        # Filter by age only when upload_date is reliably present (>50% of videos have a date).
        # yt-dlp flat-playlist often returns NA, making the age filter delete everything.
        dated = sum(1 for v in videos if v.get("upload_date") and v["upload_date"] != "NA")
        if HOME_FEED_MAX_AGE_DAYS > 0 and dated > len(videos) * 0.5:
            cutoff = time.strftime("%Y%m%d", time.gmtime(time.time() - HOME_FEED_MAX_AGE_DAYS * 86400))
            before = len(videos)
            videos = [v for v in videos if (v.get("upload_date") or "99991231") >= cutoff]
            log.info(f"Home feed: {before} raw → {len(videos)} within {HOME_FEED_MAX_AGE_DAYS}d in {time.time()-t0:.1f}s")
        else:
            log.info(f"Home feed built: {len(videos)} videos ({dated} dated) in {time.time()-t0:.1f}s")

        built_at = time.time()
        with _home_feed_lock:
            _home_feed_cache["videos"]   = videos
            _home_feed_cache["built_at"] = built_at

        _save_home_feed_disk_cache(videos, built_at)
        self._json({"videos": videos, "built_at": int(built_at), "cached": False})

    # ── IPTV lists ────────────────────────────────────────────────────────────
    def _serve_iptv_lists(self):
        base, lists, err = _scan_iptv_lists()
        if err:
            self._error(503, err)
            return
        self._json({"base_dir": base, "lists": lists})

    def _serve_iptv_streams(self, raw_list: str | None):
        target, err = self._resolve_iptv_list_path(raw_list)
        if not target:
            code = 503 if "directory not found" in err.lower() else 400
            self._error(code, err)
            return
        if not _has_supported_iptv_list_ext(target):
            self._error(400, "Unsupported IPTV list extension (use .m3u or .m3u8)")
            return
        try:
            with open(target, encoding="utf-8", errors="replace") as f:
                content = f.read()
        except Exception as e:
            self._error(500, f"Failed to read IPTV list: {e}")
            return

        streams = _parse_iptv_m3u(content)
        self._json({
            "list": {
                "name": os.path.splitext(os.path.basename(target))[0],
                "path": os.path.relpath(target, os.path.abspath(IPTV_LISTS_DIR)).replace(os.sep, "/"),
            },
            "stream_count": len(streams),
            "streams": streams,
        })

    def _serve_fmp4_direct(self, url: str):
        """Remux/transcode a live stream to fragmented MP4 for native browser <video> playback."""
        # For local files, probe codecs to skip unnecessary transcoding
        video_args: list[str]
        audio_args: list[str]
        if _is_local_media_url(url):
            vcodec, acodec = _probe_local_codecs(_ffmpeg_input_target(url))
            fname = os.path.basename(_ffmpeg_input_target(url))
            if vcodec in ("h264", "hevc"):
                video_args = ["-c:v", "copy"]
                vlog = f"video:{vcodec}→copy"
            else:
                video_args = ["-c:v", "libx264", "-preset", "ultrafast", "-tune", "zerolatency", "-crf", "23"]
                vlog = f"video:{vcodec or '?'}→h264"
            if acodec in ("aac", "mp3", ""):
                audio_args = ["-c:a", "copy"] if acodec else []
                alog = f"audio:{acodec or 'none'}→copy"
            else:
                audio_args = ["-c:a", "aac", "-b:a", "192k", "-ar", "48000", "-ac", "2"]
                alog = f"audio:{acodec}→aac"
            log.info(f"fMP4 {fname}: {vlog}, {alog}")
        else:
            video_args = ["-c:v", "libx264", "-preset", "ultrafast", "-tune", "zerolatency", "-crf", "23"]
            audio_args = ["-c:a", "aac", "-b:a", "192k", "-ar", "48000", "-ac", "2"]

        ff_cmd = [
            "ffmpeg",
            "-loglevel", "error",
            *_direct_input_args(url),
            "-i", _ffmpeg_input_target(url),
            *video_args,
            *audio_args,
            "-movflags", "frag_keyframe+empty_moov+default_base_moof",
            "-f", "mp4",
            "pipe:1",
        ]
        ff_proc = None
        try:
            ff_proc = subprocess.Popen(
                ff_cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL
            )
            self.send_response(200)
            self.send_header("Content-Type", "video/mp4")
            self.send_header("Cache-Control", "no-cache, no-store")
            self.send_header("Connection", "keep-alive")
            self.end_headers()
            while True:
                chunk = ff_proc.stdout.read(65536)
                if not chunk:
                    break
                self.wfile.write(chunk)
        except (BrokenPipeError, ConnectionResetError):
            pass
        finally:
            if ff_proc and ff_proc.poll() is None:
                try:
                    ff_proc.terminate()
                except Exception:
                    pass

    def _serve_file_bytes(self, abs_path: str):
        """Serve a local media file directly over HTTP for native browser playback."""
        import mimetypes
        ext = os.path.splitext(abs_path)[1].lower()
        mime = mimetypes.types_map.get(ext, "video/mp4")
        try:
            size = os.path.getsize(abs_path)
        except OSError as e:
            self._error(500, str(e))
            return

        try:
            range_header = self.headers.get("Range", "")
            if range_header.startswith("bytes="):
                parts = range_header[6:].split("-")
                start = int(parts[0]) if parts[0] else 0
                end   = int(parts[1]) if len(parts) > 1 and parts[1] else size - 1
                end   = min(end, size - 1)
                length = end - start + 1
                self.send_response(206)
                self.send_header("Content-Type", mime)
                self.send_header("Content-Range", f"bytes {start}-{end}/{size}")
                self.send_header("Content-Length", str(length))
                self.send_header("Accept-Ranges", "bytes")
                self.end_headers()
                with open(abs_path, "rb") as f:
                    f.seek(start)
                    remaining = length
                    while remaining > 0:
                        chunk = f.read(min(65536, remaining))
                        if not chunk:
                            break
                        self.wfile.write(chunk)
                        remaining -= len(chunk)
            else:
                self.send_response(200)
                self.send_header("Content-Type", mime)
                self.send_header("Content-Length", str(size))
                self.send_header("Accept-Ranges", "bytes")
                self.end_headers()
                with open(abs_path, "rb") as f:
                    while True:
                        chunk = f.read(65536)
                        if not chunk:
                            break
                        self.wfile.write(chunk)
        except (BrokenPipeError, ConnectionResetError):
            pass

    def _serve_local_media(self, rel_dir: str | None = None):
        base = os.path.abspath(LOCAL_MEDIA_DIR)
        if not os.path.isdir(base):
            self._error(503, f"Local media directory not found: {base}")
            return
        # Resolve the requested sub-directory (default: root)
        if rel_dir:
            target_dir = os.path.abspath(os.path.normpath(os.path.join(base, rel_dir)))
            if not (target_dir == base or target_dir.startswith(base + os.sep)):
                self._error(400, "Invalid directory path")
                return
        else:
            target_dir = base
        if not os.path.isdir(target_dir):
            self._error(404, "Directory not found")
            return
        current_rel = os.path.relpath(target_dir, base)
        if current_rel == ".":
            current_rel = ""
        folders = []
        files = []
        try:
            for name in sorted(os.listdir(target_dir), key=str.lower):
                full = os.path.join(target_dir, name)
                if os.path.islink(full):
                    full = os.path.realpath(full)
                rel = os.path.relpath(os.path.join(target_dir, name), base)
                if os.path.isdir(full):
                    folders.append({"name": name, "path": rel.replace(os.sep, "/")})
                elif os.path.isfile(full) and _has_supported_media_ext(full):
                    files.append({"name": name, "path": rel.replace(os.sep, "/")})
        except Exception as e:
            self._error(500, f"Failed to scan local media folder: {e}")
            return
        self._json({
            "base_dir": base,
            "current_dir": current_rel.replace(os.sep, "/"),
            "folders": folders,
            "files": files,
        })

    # ── Pluto TV channels ─────────────────────────────────────────────────────
    def _serve_pluto_channels(self, lang: str):
        channels, err = pluto_cache.get(lang)
        if not channels:
            if err:
                self._error(502, f"Pluto TV [{lang}] unavailable: {err}")
            else:
                self._error(503, "Pluto TV channel list not loaded yet, try again shortly")
            return
        meta = pluto_cache.get_meta(lang)
        self._json({
            "lang": lang,
            "country": meta.get("country", ""),
            "region": meta.get("region", ""),
            "xff": meta.get("xff", ""),
            "refresh_at": meta.get("refresh_at", 0),
            "channels": channels,
        })

    # ── Feed ──────────────────────────────────────────────────────────────────
    def _serve_feed(self, channel: str, limit: int):
        # Normalise: bare handle (@channel), channel URL, or plain name
        if channel.startswith("http://") or channel.startswith("https://"):
            url = channel
        elif channel.startswith("@"):
            url = f"https://www.youtube.com/{channel}/videos"
        else:
            url = f"https://www.youtube.com/@{channel}/videos"

        try:
            r = subprocess.run(
                [
                    "yt-dlp",
                    "--js-runtimes", "node",
                    "--flat-playlist",
                    "--playlist-end", str(limit),
                    "--print", "%(id)s\t%(title)s\t%(duration)s\t%(thumbnail)s\t%(webpage_url)s",
                    "--no-warnings",
                    "--quiet",
                    *_yt_lang_args(),
                    url,
                ],
                capture_output=True, text=True, timeout=20,
            )
        except subprocess.TimeoutExpired:
            self._error(504, "yt-dlp timed out fetching feed")
            return
        except Exception as e:
            self._error(500, f"Feed fetch failed: {e}")
            return

        if r.returncode != 0:
            err = r.stderr.strip() or "yt-dlp returned non-zero exit code"
            self._error(502, f"Could not fetch channel feed: {err}")
            return

        videos = []
        for line in r.stdout.strip().splitlines():
            parts = line.split("\t", 4)
            if len(parts) < 2:
                continue
            vid_id   = parts[0].strip()
            title    = parts[1].strip()
            duration = parts[2].strip() if len(parts) > 2 else ""
            thumb    = parts[3].strip() if len(parts) > 3 else ""
            webpage  = parts[4].strip() if len(parts) > 4 else ""
            if not vid_id or vid_id == "NA":
                continue
            # Use the canonical webpage URL when available; fall back to
            # building a YouTube URL from the ID for backwards compatibility.
            if webpage and webpage != "NA":
                video_url = webpage
            else:
                video_url = f"https://www.youtube.com/watch?v={vid_id}"
            # yt-dlp returns NA for thumbnails in flat-playlist mode on YouTube.
            # The thumbnail URL is deterministic from the video ID.
            if (not thumb or thumb == "NA") and "youtube.com" in video_url:
                thumb = f"https://i.ytimg.com/vi/{vid_id}/mqdefault.jpg"
            videos.append({
                "id":       vid_id,
                "title":    title,
                "duration": duration,
                "thumb":    thumb,
                "url":      video_url,
            })

        self._json({"channel": url, "videos": videos})

    def _serve_ytsearch(self, query: str, limit: int = 12):
        search_url = f"ytsearch{limit}:{query}"
        try:
            r = subprocess.run(
                [
                    "yt-dlp",
                    "--js-runtimes", "node",
                    "--flat-playlist",
                    "--print", "%(id)s\t%(title)s\t%(duration)s\t%(thumbnail)s\t%(webpage_url)s",
                    "--no-warnings",
                    "--quiet",
                    *_yt_lang_args(),
                    search_url,
                ],
                capture_output=True, text=True, timeout=25,
            )
        except subprocess.TimeoutExpired:
            self._error(504, "yt-dlp timed out during search")
            return
        except Exception as e:
            self._error(500, f"Search failed: {e}")
            return

        if r.returncode != 0:
            err = r.stderr.strip() or "yt-dlp returned non-zero exit code"
            self._error(502, f"Search failed: {err}")
            return

        videos = []
        for line in r.stdout.strip().splitlines():
            parts = line.split("\t", 4)
            if len(parts) < 2:
                continue
            vid_id   = parts[0].strip()
            title    = parts[1].strip()
            duration = parts[2].strip() if len(parts) > 2 else ""
            thumb    = parts[3].strip() if len(parts) > 3 else ""
            webpage  = parts[4].strip() if len(parts) > 4 else ""
            if not vid_id or vid_id == "NA":
                continue
            if webpage and webpage != "NA":
                video_url = webpage
            else:
                video_url = f"https://www.youtube.com/watch?v={vid_id}"
            if (not thumb or thumb == "NA"):
                thumb = f"https://i.ytimg.com/vi/{vid_id}/mqdefault.jpg"
            videos.append({
                "id":       vid_id,
                "title":    title,
                "duration": duration,
                "thumb":    thumb,
                "url":      video_url,
            })

        self._json({"videos": videos})

    # ── MJPEG ─────────────────────────────────────────────────────────────────
    def _serve_mjpeg(self, stream: Stream, sync_ms: int = 0):
        registry.cleanup_done()
        delay_s = max(0.0, sync_ms / 1000.0)

        # Start pipeline if not already running
        if stream.status == "starting" and stream._ff_proc is None:
            threading.Thread(target=run_pipeline,
                             args=(stream,), daemon=True).start()

        # Wait up to 60s for first frame (yt-dlp alone can take 15-20s on a Pi)
        deadline = time.time() + 60
        with stream.frame_cond:
            while stream.frame is None and stream.status not in ("error", "done"):
                if time.time() > deadline:
                    self._error(504, "Timed out waiting for first frame")
                    return
                stream.frame_cond.wait(timeout=0.5)
        if delay_s > 0:
            # Let delayed playback have enough buffered frames so the first
            # shown frame starts near content time 0.
            with stream.frame_cond:
                while stream.status not in ("error", "done"):
                    if stream._frame_history:
                        oldest_ts = stream._frame_history[0][0]
                        newest_ts = stream._frame_history[-1][0]
                        if newest_ts - oldest_ts >= delay_s:
                            break
                    if time.time() > deadline:
                        break
                    stream.frame_cond.wait(timeout=0.5)

        if stream.status == "error":
            detail = f" ({stream.error_detail})" if stream.error_detail else ""
            self._error(502, f"Pipeline error: {stream.error}{detail}")
            return
        if stream.status == "done" and stream.frame is None:
            detail = f" ({stream.error_detail})" if stream.error_detail else ""
            self._error(502, f"Video ended before first frame was produced{detail}")
            return

        self.send_response(200)
        self.send_header("Content-Type",  "multipart/x-mixed-replace; boundary=frame")
        self.send_header("Cache-Control", "no-cache, no-store")
        self.send_header("Connection",    "keep-alive")
        self.send_header("X-Stream-Id",   stream.id)
        self.send_header("X-Stream-Title", self._safe_header_value(stream.title or ""))
        self.end_headers()

        log.info(f"[{stream.id}] Client connected: {self.client_address[0]}")
        last_frame = None

        try:
            while True:
                # Wait for FFmpeg to produce a new frame (wakes all clients immediately).
                with stream.frame_cond:
                    stream.frame_cond.wait(timeout=5.0)
                    if delay_s <= 0:
                        frame = stream.frame
                    else:
                        cutoff = time.time() - delay_s
                        frame = None
                        for ts, candidate in reversed(stream._frame_history):
                            if ts <= cutoff:
                                frame = candidate
                                break
                    status = stream.status

                if frame and frame is not last_frame:
                    last_frame = frame
                    boundary = (
                        b"--frame\r\n"
                        b"Content-Type: image/jpeg\r\n"
                        b"Content-Length: " + str(len(frame)).encode() + b"\r\n\r\n"
                    )
                    self.wfile.write(boundary + frame + b"\r\n")

                if status in ("error", "done"):
                    break

        except (BrokenPipeError, ConnectionResetError):
            log.info(f"[{stream.id}] Client disconnected: {self.client_address[0]}")

    @staticmethod
    def _launch_audio_pipeline(url: str, seek_s: float):
        """Spawn ffmpeg for audio starting at seek_s seconds.
        Always resolves a direct CDN URL first so ffmpeg reads at real-time
        pace and never buffers a whole long video into a pipe."""
        audio_fmt = "bestaudio[ext=m4a]/bestaudio"
        url_r = subprocess.run(
            ["yt-dlp", "--js-runtimes", "node", "--no-playlist",
             "-f", audio_fmt, "--get-url", "--quiet", url],
            capture_output=True, text=True, timeout=30,
        )
        direct_url = url_r.stdout.strip().splitlines()[0] if url_r.returncode == 0 else ""

        if direct_url:
            seek_args = ["-ss", str(int(seek_s))] if seek_s > 0 else []
            ff_cmd = [
                "ffmpeg", "-loglevel", "error",
                "-reconnect", "1",
                "-reconnect_streamed", "1",
                "-reconnect_delay_max", "10",
                *seek_args,
                "-i", direct_url,
                "-vn",
                "-af", "aresample=async=1:first_pts=0",
                "-c:a", "mp3", "-b:a", "128k", "-f", "mp3", "pipe:1",
            ]
            ff_proc = subprocess.Popen(ff_cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
            return None, ff_proc

        # Fallback: pipe yt-dlp → ffmpeg
        yt_cmd = [
            "yt-dlp", "--js-runtimes", "node", "--no-playlist",
            "-f", audio_fmt, "-o", "-", "--quiet", url,
        ]
        ff_cmd = [
            "ffmpeg", "-loglevel", "error",
            "-i", "pipe:0", "-vn",
            "-af", "aresample=async=1:first_pts=0",
            "-c:a", "mp3", "-b:a", "128k", "-f", "mp3", "pipe:1",
        ]
        yt_proc = subprocess.Popen(yt_cmd, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        ff_proc = subprocess.Popen(ff_cmd, stdin=yt_proc.stdout,
                                   stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        return yt_proc, ff_proc

    def _serve_audio(self, stream: Stream, sync_ms: int = AUDIO_DELAY_MS):
        log.info(f"[{stream.id}] Audio starting (audio_only={stream.audio_only})")

        # audio_only mode: pipeline uses _start_audio_buffer_any which always
        # fills _audio_chunks regardless of stream type. Start pipeline if needed.
        if stream.audio_only:
            if stream.status == "starting" and stream._audio_proc is None:
                threading.Thread(target=run_pipeline,
                                 args=(stream,), daemon=True).start()
            try:
                self.send_response(200)
                self.send_header("Content-Type", "audio/mpeg")
                self.send_header("Cache-Control", "no-cache, no-store")
                self.send_header("Connection", "keep-alive")
                self.end_headers()
                cursor = 0
                sent_bytes = 0
                while True:
                    stream._audio_ready.wait(timeout=5)
                    stream._audio_ready.clear()
                    with stream._audio_lock:
                        new_chunks = stream._audio_chunks[cursor:]
                        cursor += len(new_chunks)
                        done = stream._audio_done
                    for ch in new_chunks:
                        self.wfile.write(ch)
                        sent_bytes += len(ch)
                    self.wfile.flush()
                    if done and not new_chunks:
                        break
                log.info(f"[{stream.id}] Audio-only stream ended (bytes={sent_bytes})")
            except (BrokenPipeError, ConnectionResetError):
                pass
            return

        if _is_direct_stream(stream.url):
            # MJPEG mode: audio is captured into _audio_chunks by the muxed pipeline.
            # Start the pipeline here if /audio is requested before /stream.
            if stream.status == "starting" and stream._ff_proc is None:
                threading.Thread(target=run_pipeline,
                                 args=(stream,), daemon=True).start()
            try:
                self.send_response(200)
                self.send_header("Content-Type", "audio/mpeg")
                self.send_header("Cache-Control", "no-cache, no-store")
                self.send_header("Connection", "keep-alive")
                self.end_headers()

                cursor = 0
                sent_bytes = 0
                while True:
                    stream._audio_ready.wait(timeout=5)
                    stream._audio_ready.clear()
                    with stream._audio_lock:
                        new_chunks = stream._audio_chunks[cursor:]
                        cursor += len(new_chunks)
                        done = stream._audio_done
                    for ch in new_chunks:
                        self.wfile.write(ch)
                        sent_bytes += len(ch)
                    self.wfile.flush()
                    if done and not new_chunks:
                        break
                log.info(f"[{stream.id}] Direct audio ended (bytes={sent_bytes})")
            except (BrokenPipeError, ConnectionResetError):
                pass
            return

        # MJPEG mode, non-direct (YouTube/Twitch): independent audio pipeline
        yt_proc = None
        ff_proc = None
        try:
            yt_proc, ff_proc = self._launch_audio_pipeline(stream.url, seek_s=stream.seek_s)

            self.send_response(200)
            self.send_header("Content-Type", "audio/mpeg")
            self.send_header("Cache-Control", "no-cache, no-store")
            self.send_header("Connection", "keep-alive")
            self.end_headers()

            while True:
                chunk = ff_proc.stdout.read(16384)
                if not chunk:
                    break
                self.wfile.write(chunk)
                self.wfile.flush()
        except (BrokenPipeError, ConnectionResetError):
            pass
        finally:
            for proc in (ff_proc, yt_proc):
                if proc:
                    try:
                        proc.terminate()
                    except Exception:
                        pass

    # ── Helpers ───────────────────────────────────────────────────────────────
    def _html(self, body: str, code: int = 200):
        data = body.encode()
        self.send_response(code)
        self.send_header("Content-Type",   "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def _json(self, obj, code: int = 200):
        data = json.dumps(obj, indent=2).encode()
        self.send_response(code)
        self.send_header("Content-Type",   "application/json")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def _error(self, code: int, msg: str):
        self._json({"error": msg, "code": code}, code)


class ThreadedHTTPServer(ThreadingMixIn, HTTPServer):
    """Each request handled in its own thread (needed for concurrent MJPEG streams)."""
    daemon_threads = True
    allow_reuse_address = True


# ── Main ──────────────────────────────────────────────────────────────────────
def main():
    log.info("═" * 52)
    log.info("  OpenCarStream MJPEG Streamer")
    log.info(f"  Listening on http://{HOST}:{PORT}")
    log.info(f"  FPS={MJPEG_FPS}  Quality={FFMPEG_QUALITY}  "
             f"Res={STREAM_WIDTH}×{STREAM_HEIGHT}  MaxStreams={MAX_STREAMS}")
    log.info("═" * 52)

    pluto_cache.start_background_refresh()
    _load_home_feed_disk_cache()

    def _stream_reaper():
        while True:
            time.sleep(60)
            registry.cleanup_old()
    threading.Thread(target=_stream_reaper, daemon=True).start()

    def _home_feed_refresher():
        """Build home feed on startup then refresh every 6 hours."""
        # Small delay so the server is ready before the first fetch
        time.sleep(5)
        while True:
            if not os.path.isfile(SUBSCRIPTIONS_FILE):
                time.sleep(300)
                continue
            try:
                with open(SUBSCRIPTIONS_FILE, encoding="utf-8") as f:
                    data = json.load(f)
                channels = data.get("channels", [])
            except Exception:
                channels = []
            if channels:
                log.info(f"Background home feed refresh ({len(channels)} channels)…")
                t0 = time.time()
                videos = _build_home_feed(channels)
                built_at = time.time()
                with _home_feed_lock:
                    _home_feed_cache["videos"]   = videos
                    _home_feed_cache["built_at"] = built_at
                _save_home_feed_disk_cache(videos, built_at)
                log.info(f"Background home feed done: {len(videos)} videos in {built_at-t0:.1f}s")
            time.sleep(6 * 3600)
    threading.Thread(target=_home_feed_refresher, daemon=True).start()

    server = ThreadedHTTPServer((HOST, PORT), Handler)

    def _stop(sig, frame):
        log.info("Shutting down…")
        for s in registry.all_streams():
            s.stop()
        server.shutdown()
        sys.exit(0)

    signal.signal(signal.SIGINT,  _stop)
    signal.signal(signal.SIGTERM, _stop)
    server.serve_forever()


if __name__ == "__main__":
    main()
