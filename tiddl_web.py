"""
tiddl web — a simple browser UI for the tiddl Tidal downloader.

A Monochrome-inspired Tidal-like web interface (zero extra dependencies, uses
Python's stdlib http.server). It reuses the tiddl backend for search/listing
and the tiddl CLI for downloading (so already-downloaded tracks are skipped
automatically).

Run it with the project's virtual environment:

    .venv\\Scripts\\python.exe tiddl_web.py        (Windows)
    .venv/bin/python tiddl_web.py                  (macOS / Linux)

Then open http://127.0.0.1:8765 in your browser.
You can log in straight from the web page.
"""

from __future__ import annotations

import os
import re
import sys
import json
import base64
import hashlib
import secrets
import threading
import subprocess
import webbrowser
import requests
from pathlib import Path
from time import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urlparse, parse_qs, urlencode

# Hi-Res login uses the PKCE flow with python-tidal's Hi-Res client. Set it as
# TIDDL_AUTH (before importing tiddl.core.auth) so token refresh uses the same
# client. This client unlocks Hi-Res (24-bit) streams for a subscribed account.
PKCE_CLIENT_ID = "6BDSRdpK9hqEBTgU"
PKCE_CLIENT_SECRET = "xeuPmY7nbpZ9IIbLAcQ93shka1VNheUAqN6IcszjTG8="
PKCE_REDIRECT_URI = "https://tidal.com/android/login/auth"
os.environ.setdefault("TIDDL_AUTH", f"{PKCE_CLIENT_ID};{PKCE_CLIENT_SECRET}")

from tiddl.cli.config import CONFIG, APP_PATH
from tiddl.core.api import TidalClient, TidalAPI
from tiddl.core.auth import AuthAPI, AuthClientError
from tiddl.cli.utils.auth.core import load_auth_data, save_auth_data, AuthData
from tiddl.core.utils.sanitize import sanitize_string

HOST, PORT = "127.0.0.1", 8765
AUDIO_EXTENSIONS = {".flac", ".m4a", ".mp4", ".mp3", ".ts"}
QUALITIES = ["low", "normal", "high", "max"]
ATMOS_FILTERS = ["none", "allow", "only"]
MAX_CONCURRENCY = 4  # max albums downloaded in parallel
MAX_THREADS = 16     # max track-download threads within one album

# Use title_version so tracks that share a title but differ by version
# (e.g. "Radio Edit" vs "Spanglish Radio Edit") don't collide on disk.
OUTPUT_TEMPLATE = "{album.artist}/{album.title}/{item.title_version}"

# Maps a download folder name -> {id, name, picture} so the library knows
# exactly which Tidal artist each downloaded folder belongs to.
REGISTRY_FILE = APP_PATH / "web_artists.json"

# Persisted UI settings (download path, quality) so they survive restarts.
SETTINGS_FILE = APP_PATH / "web_settings.json"


def load_settings() -> dict:
    try:
        return json.loads(SETTINGS_FILE.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def save_settings(download_path: str, quality: str, atmos: str, overwrite: bool,
                  concurrency: int, threads: int) -> None:
    try:
        SETTINGS_FILE.write_text(
            json.dumps({"download_path": download_path, "quality": quality,
                        "atmos": atmos, "overwrite": overwrite,
                        "concurrency": concurrency, "threads": threads},
                       ensure_ascii=False, indent=2),
            encoding="utf-8",
        )
    except OSError:
        pass


# ---------------------------------------------------------------------------
# Shared state
# ---------------------------------------------------------------------------
class State:
    def __init__(self) -> None:
        self.lock = threading.Lock()
        saved = load_settings()
        self.download_path = saved.get("download_path") or str(CONFIG.download.download_path)
        self.quality = saved.get("quality") if saved.get("quality") in QUALITIES else "max"
        self.atmos = saved.get("atmos") if saved.get("atmos") in ATMOS_FILTERS else "none"
        self.overwrite = bool(saved.get("overwrite", False))
        self.queue: list[dict] = []
        self.queue_counter = 0
        self.workers = 0  # number of running worker threads
        self.concurrency = min(max(int(saved.get("concurrency", 1) or 1), 1), MAX_CONCURRENCY)
        self.threads = min(max(int(saved.get("threads", 4) or 4), 1), MAX_THREADS)
        self.current_procs: dict[str, subprocess.Popen] = {}  # qid -> process
        self.login = {"active": False, "url": "", "message": "", "done": False}
        self.pkce: dict = {}  # verifier + client_unique_key for the active PKCE login
        self.cover_job: dict = {"running": False, "saved": 0, "exists": 0,
                                "nocover": 0, "failed": 0, "no_data": 0,
                                "total_artists": 0, "done_artists": 0}


STATE = State()


# ---------------------------------------------------------------------------
# Backend helpers
# ---------------------------------------------------------------------------
def build_api() -> TidalAPI:
    auth_data = load_auth_data()
    if not (auth_data.token and auth_data.user_id and auth_data.country_code):
        raise RuntimeError("Not logged in")

    refresh_token = auth_data.refresh_token
    if not refresh_token:
        raise RuntimeError("Refresh token missing")

    auth_api = AuthAPI()

    def on_token_expiry() -> str | None:
        resp = auth_api.refresh_token(refresh_token)
        auth_data.token = resp.access_token
        auth_data.expires_at = resp.expires_in + int(time())
        save_auth_data(auth_data=auth_data)
        return resp.access_token if resp else None

    client = TidalClient(
        token=auth_data.token,
        cache_name=APP_PATH / "api_cache",
        on_token_expiry=on_token_expiry,
    )
    return TidalAPI(client, auth_data.user_id, auth_data.country_code)


def clean_segment(text: str) -> str:
    text = sanitize_string(text)
    text = re.sub(r"\.{2,}", ".", text)
    text = text.rstrip(" .")
    text = re.sub(r"\s{2,}", " ", text)
    return text.strip() or "_"


def album_dir(download_path: Path, artist_name: str, album_title: str) -> Path:
    return download_path / clean_segment(artist_name) / clean_segment(album_title)


def count_audio_files(directory: Path) -> int:
    if not directory.is_dir():
        return 0
    return sum(
        1 for p in directory.rglob("*")
        if p.is_file() and p.suffix.lower() in AUDIO_EXTENSIONS
    )


def album_format(album) -> str:
    """Human-readable format from catalog tags (accurate with a Hi-Res client)."""
    tags = album.mediaMetadata.tags or []
    parts = []
    if "HIRES_LOSSLESS" in tags:
        parts.append("Hi-Res")
    elif "LOSSLESS" in tags:
        parts.append("Lossless")
    if "DOLBY_ATMOS" in tags:
        parts.append("Atmos")
    return " · ".join(parts)


def quality_label(quality: str, tags) -> str:
    """Friendly per-track quality label."""
    if "DOLBY_ATMOS" in (tags or []):
        return "Atmos"
    return {
        "LOW": "AAC", "HIGH": "AAC 320",
        "LOSSLESS": "FLAC", "HI_RES_LOSSLESS": "Hi-Res FLAC",
    }.get(quality, quality or "")


def file_audio_info(path: Path) -> dict:
    """Real specs of a downloaded file: size (bytes), bit depth, sample rate."""
    info = {"size": None, "bits": None, "sampleRate": None}
    try:
        info["size"] = path.stat().st_size
    except OSError:
        pass
    try:
        from mutagen import File as _MF
        mf = _MF(str(path))
        if mf is not None and mf.info is not None:
            info["sampleRate"] = getattr(mf.info, "sample_rate", None)
            info["bits"] = getattr(mf.info, "bits_per_sample", None) or None
    except Exception:  # noqa: BLE001
        pass
    return info


def album_status(download_path: Path, artist_name: str, album, folder_title: str | None = None,
                 total_override: int | None = None) -> dict:
    d = album_dir(download_path, artist_name, folder_title or album.title)
    n = count_audio_files(d)
    # Tidal's numberOfTracks can exceed the actually-available tracks (some are
    # removed/region-locked). Use the real count cached from the popup if known.
    total = total_override or album.numberOfTracks
    if n > 0 and n >= total:
        state, label = "done", f"Downloaded · {n}"
    elif n > 0:
        state, label = "partial", f"Partial · {n}/{total}"
    else:
        state, label = "none", "Not downloaded"
    year = ""
    if album.releaseDate:
        year = str(album.releaseDate.year)
    return {
        "id": album.id,
        "title": album.title,
        "cover": album.cover,
        "year": year,
        "numberOfTracks": total,
        "state": state,
        "statusLabel": label,
        "format": album_format(album),
    }


def load_registry() -> dict:
    try:
        return json.loads(REGISTRY_FILE.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def register_artist(artist_id, name: str, picture) -> None:
    """Remember which Tidal artist a download folder belongs to."""
    if not name:
        return
    with STATE.lock:
        reg = load_registry()
        reg[clean_segment(name)] = {
            "id": str(artist_id), "name": name, "picture": picture,
        }
        try:
            REGISTRY_FILE.write_text(json.dumps(reg, ensure_ascii=False, indent=2),
                                     encoding="utf-8")
        except OSError:
            pass


def open_folder(path: Path) -> bool:
    """Open a folder in the OS file explorer (server runs on the user's machine)."""
    if not path.exists():
        return False
    try:
        if os.name == "nt":
            os.startfile(str(path))  # noqa: S606
        elif sys.platform == "darwin":
            subprocess.Popen(["open", str(path)])
        else:
            subprocess.Popen(["xdg-open", str(path)])
        return True
    except Exception:  # noqa: BLE001
        return False


ARTIST_CACHE_DIR = APP_PATH / "artist_cache"
ALBUM_COUNT_FILE = APP_PATH / "album_counts.json"  # album_id -> real downloadable track count


def load_album_counts() -> dict:
    try:
        return json.loads(ALBUM_COUNT_FILE.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError):
        return {}


def save_album_count(aid: str, count: int) -> None:
    try:
        counts = load_album_counts()
        if counts.get(str(aid)) == count:
            return
        counts[str(aid)] = count
        ALBUM_COUNT_FILE.write_text(json.dumps(counts), encoding="utf-8")
    except OSError:
        pass


def save_artist_cache(aid: str, data: dict) -> None:
    try:
        ARTIST_CACHE_DIR.mkdir(exist_ok=True)
        (ARTIST_CACHE_DIR / f"{aid}.json").write_text(
            json.dumps(data, ensure_ascii=False), encoding="utf-8")
    except OSError:
        pass


def load_artist_cache(aid: str) -> dict | None:
    try:
        return json.loads((ARTIST_CACHE_DIR / f"{aid}.json").read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError):
        return None


def recompute_album_state(alb: dict, base: Path) -> None:
    """Refresh an album dict's downloaded badge from the local filesystem (offline)."""
    folder_title = f"{alb['title']} [{alb['id']}]" if alb.get("dup") else alb["title"]
    n = count_audio_files(album_dir(base, alb.get("folder_artist", ""), folder_title))
    total = alb.get("numberOfTracks", 0)
    if n > 0 and n >= total:
        alb["state"], alb["statusLabel"] = "done", f"Downloaded · {n}"
    elif n > 0:
        alb["state"], alb["statusLabel"] = "partial", f"Partial · {n}/{total}"
    else:
        alb["state"], alb["statusLabel"] = "none", "Not downloaded"


def save_album_cover(cover_id: str, directory: Path, size: int = 1280,
                     overwrite: bool = False) -> str:
    """Download an album's cover image as cover.jpg into its folder."""
    if not directory.is_dir():
        return "missing"          # album not downloaded
    if not cover_id:
        return "nocover"          # no cover available
    dest = directory / "cover.jpg"
    if dest.exists() and not overwrite:
        return "exists"
    url = f"https://resources.tidal.com/images/{cover_id.replace('-', '/')}/{size}x{size}.jpg"
    try:
        r = requests.get(url, timeout=20)
        if r.status_code == 200 and r.content:
            dest.write_bytes(r.content)
            return "saved"
        return "failed"
    except Exception:  # noqa: BLE001
        return "failed"


def artist_album_cover_list(api, aid: str) -> list[dict]:
    """Fetch {id, title, cover, dup} for all of an artist's albums + singles."""
    from collections import Counter
    raw = []
    for filt in ("ALBUMS", "EPSANDSINGLES"):
        off = 0
        while True:
            p = api.get_artist_albums(artist_id=aid, offset=off, filter=filt, limit=50)
            for alb in p.items:
                raw.append(alb)
            off += p.limit
            if off >= p.totalNumberOfItems:
                break
    counts = Counter(a.title.lower() for a in raw)
    return [{"id": a.id, "title": a.title, "cover": a.cover,
             "dup": counts[a.title.lower()] > 1} for a in raw]


def run_covers_all() -> None:
    """Background: save cover.jpg into every downloaded album folder (skip existing)."""
    base = Path(STATE.download_path)
    reg_lower = {k.lower(): v for k, v in load_registry().items()}
    job = STATE.cover_job
    with STATE.lock:
        job.update({"running": True, "saved": 0, "exists": 0, "nocover": 0,
                    "failed": 0, "no_data": 0, "done_artists": 0})
        job["total_artists"] = sum(1 for d in base.iterdir() if d.is_dir()) if base.is_dir() else 0
    api = None
    try:
        if not base.is_dir():
            return
        for d in sorted(base.iterdir(), key=lambda p: p.name.lower()):
            if not d.is_dir():
                continue
            meta = reg_lower.get(d.name.lower())
            aid = meta.get("id") if meta else None
            albums = None
            if aid:
                cached = load_artist_cache(aid)
                if cached:
                    albums = cached.get("albums", []) + cached.get("singles", [])
                else:
                    try:
                        if api is None:
                            api = build_api()
                        albums = artist_album_cover_list(api, aid)
                    except Exception:  # noqa: BLE001
                        albums = None
            if not albums:
                with STATE.lock:
                    job["no_data"] += 1
                    job["done_artists"] += 1
                continue
            for al in albums:
                folder = f"{al['title']} [{al['id']}]" if al.get("dup") else al["title"]
                adir = album_dir(base, d.name, folder)
                if adir.is_dir():
                    r = save_album_cover(al.get("cover", ""), adir)
                    with STATE.lock:
                        job[r if r in job else "failed"] += 1
            with STATE.lock:
                job["done_artists"] += 1
    finally:
        with STATE.lock:
            job["running"] = False


def find_tiddl_executable() -> list[str]:
    scripts_dir = Path(sys.executable).parent
    for c in (scripts_dir / ("tiddl.exe" if os.name == "nt" else "tiddl"),):
        if c.exists():
            return [str(c)]
    return [sys.executable, "-m", "tiddl.cli.app"]


# ---------------------------------------------------------------------------
# Login (device flow) — runs in background
# ---------------------------------------------------------------------------
def start_login() -> dict:
    with STATE.lock:
        if STATE.login["active"]:
            return dict(STATE.login)

    existing = load_auth_data()
    if existing.token:
        STATE.login = {"active": False, "url": "", "message": "Already logged in.", "done": True}
        return dict(STATE.login)

    auth_api = AuthAPI()
    device = auth_api.get_device_auth()
    url = f"https://{device.verificationUriComplete}"
    STATE.login = {"active": True, "url": url, "message": "Open the link and authenticate...", "done": False}

    def poll():
        auth_end = time() + device.expiresIn
        while time() < auth_end:
            threading.Event().wait(device.interval)
            try:
                auth = auth_api.get_auth(device.deviceCode)
                save_auth_data(AuthData(
                    token=auth.access_token,
                    refresh_token=auth.refresh_token,
                    expires_at=auth.expires_in + int(time()),
                    user_id=str(auth.user_id),
                    country_code=auth.user.countryCode,
                ))
                with STATE.lock:
                    STATE.login = {"active": False, "url": "", "message": "Logged in!", "done": True}
                return
            except AuthClientError as e:
                if e.error == "authorization_pending":
                    continue
                if e.error == "expired_token":
                    with STATE.lock:
                        STATE.login = {"active": False, "url": "", "message": "Authentication expired, try again.", "done": False}
                    return
            except Exception as e:  # noqa: BLE001 — don't let the poll thread die silently
                with STATE.lock:
                    STATE.login = {"active": False, "url": "", "message": f"Login error: {e}", "done": False}
                return
        with STATE.lock:
            STATE.login = {"active": False, "url": "", "message": "Authentication expired.", "done": False}

    threading.Thread(target=poll, daemon=True).start()
    return dict(STATE.login)


# ---------------------------------------------------------------------------
# PKCE Hi-Res login (browser authorization-code flow)
# ---------------------------------------------------------------------------
def pkce_start() -> str:
    """Create a PKCE challenge and return the Tidal authorize URL."""
    verifier = base64.urlsafe_b64encode(os.urandom(32)).rstrip(b"=").decode()
    challenge = base64.urlsafe_b64encode(
        hashlib.sha256(verifier.encode()).digest()
    ).rstrip(b"=").decode()
    uniq = secrets.token_hex(8)
    with STATE.lock:
        STATE.pkce = {"verifier": verifier, "uniq": uniq}
    params = {
        "response_type": "code",
        "redirect_uri": PKCE_REDIRECT_URI,
        "client_id": PKCE_CLIENT_ID,
        "lang": "en",
        "appMode": "android",
        "client_unique_key": uniq,
        "code_challenge": challenge,
        "code_challenge_method": "S256",
        "restrict_signup": "true",
        "scope": "r_usr w_usr",
    }
    return "https://login.tidal.com/authorize?" + urlencode(params)


def pkce_finish(redirect_url: str) -> dict:
    """Exchange the authorization code (from the pasted redirect URL) for tokens."""
    qs = parse_qs(urlparse(redirect_url.strip()).query)
    code = qs.get("code", [""])[0]
    if not code:
        # allow pasting the raw code too
        code = redirect_url.strip()
    if not code:
        return {"ok": False, "error": "No code found in the URL."}

    with STATE.lock:
        pkce = dict(STATE.pkce)
    if not pkce.get("verifier"):
        return {"ok": False, "error": "Login session expired, click Log in again."}

    res = requests.post(
        "https://auth.tidal.com/v1/oauth2/token",
        data={
            "client_id": PKCE_CLIENT_ID,
            "code": code,
            "grant_type": "authorization_code",
            "redirect_uri": PKCE_REDIRECT_URI,
            "scope": "r_usr w_usr",
            "code_verifier": pkce["verifier"],
            "client_unique_key": pkce["uniq"],
        },
        auth=(PKCE_CLIENT_ID, PKCE_CLIENT_SECRET),
        timeout=20,
    )
    if res.status_code != 200:
        try:
            msg = res.json().get("error_description", res.text[:120])
        except Exception:  # noqa: BLE001
            msg = res.text[:120]
        return {"ok": False, "error": f"{res.status_code}: {msg}"}

    j = res.json()
    user = j.get("user", {})
    save_auth_data(AuthData(
        token=j["access_token"], refresh_token=j["refresh_token"],
        expires_at=j["expires_in"] + int(time()),
        user_id=str(j.get("user_id")), country_code=user.get("countryCode"),
    ))
    with STATE.lock:
        STATE.pkce = {}
    return {"ok": True, "user_id": j.get("user_id"), "country": user.get("countryCode")}


# ---------------------------------------------------------------------------
# Download queue (sequential worker, cancellable)
# ---------------------------------------------------------------------------
def enqueue(items: list[dict], path: str, quality: str) -> list[str]:
    """Add items to the queue and ensure the worker is running."""
    ids = []
    with STATE.lock:
        for it in items:
            STATE.queue_counter += 1
            qid = f"q{STATE.queue_counter}"
            STATE.queue.append({
                "id": qid,
                "resource": it["resource"],
                "title": it.get("title", it["resource"]),
                "kind": it.get("kind", ""),
                "artist": it.get("artist", ""),
                "cover": it.get("cover", ""),
                "folder": it.get("folder", ""),
                "template": it.get("template", ""),
                "path": path,
                "quality": quality,
                "atmos": STATE.atmos,
                "overwrite": STATE.overwrite,
                "threads": STATE.threads,
                "status": "queued",   # queued|downloading|done|error|cancelled
                "file": "",
                "log": [],
                "track_total": int(it.get("total", 0) or 0),
                "track_done": 0,
            })
            ids.append(qid)
    ensure_workers()
    return ids


def ensure_workers() -> None:
    """Spawn worker threads up to the configured concurrency (if work is queued)."""
    with STATE.lock:
        queued_n = sum(1 for e in STATE.queue if e["status"] == "queued")
        to_start = max(0, min(STATE.concurrency, queued_n) - STATE.workers)
        STATE.workers += to_start
    for _ in range(to_start):
        threading.Thread(target=_worker_loop, daemon=True).start()


def _worker_loop():
    exe = find_tiddl_executable()
    while True:
        with STATE.lock:
            entry = next((e for e in STATE.queue if e["status"] == "queued"), None)
            if entry is None:
                STATE.workers -= 1
                return
            entry["status"] = "downloading"
            entry["file"] = ""
            entry["track_done"] = 0
            qid = entry["id"]
            path, quality = entry["path"], entry["quality"]
            template = entry["template"] or OUTPUT_TEMPLATE
            atmos = entry["atmos"]
            resource = entry["resource"]
            overwrite = entry.get("overwrite", False)
            threads = entry.get("threads", 4)

        cmd = exe + ["download", "-p", path, "--sp", path, "-q", quality,
                     "-da", atmos, "-t", str(threads), "-o", template]
        if overwrite:
            cmd.append("-ns")  # --no-skip: re-download even if the file exists
        cmd += ["url", resource]
        try:
            # Force the child to emit UTF-8 so rich can print non-Latin track
            # names (Korean/Japanese/etc.) without crashing on Windows cp1252.
            child_env = {**os.environ, "PYTHONUTF8": "1", "PYTHONIOENCODING": "utf-8"}
            proc = subprocess.Popen(
                cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, encoding="utf-8", errors="replace", bufsize=1,
                cwd=str(Path(__file__).parent), env=child_env,
            )
            with STATE.lock:
                STATE.current_procs[qid] = proc
            assert proc.stdout is not None
            tail: list[str] = []
            last_error = ""
            for line in proc.stdout:
                line = line.strip()
                if not line:
                    continue
                low = line.lower()
                tail.append(line)
                del tail[:-25]  # keep last 25 lines
                # capture anything that looks like an error/skip reason
                if ("error" in low or low.startswith(("can't stream", "skipping"))):
                    last_error = line
                # each track emits one result line — count it for per-album progress
                if low.startswith(("downloaded", "exists", "overwrited", "skipping", "can't stream")):
                    with STATE.lock:
                        entry["track_done"] += 1
                if low.startswith(("downloaded", "exists", "overwrited")) or os.sep in line:
                    with STATE.lock:
                        entry["file"] = line
                with STATE.lock:
                    entry["log"] = list(tail)
            proc.wait()
            cancelled = False
            with STATE.lock:
                if entry["status"] == "cancelling":
                    entry["status"] = "cancelled"
                    cancelled = True
                elif proc.returncode == 0:
                    entry["status"] = "done"
                else:
                    entry["status"] = "error"
                    entry["file"] = last_error or f"Error (exit code {proc.returncode})"
                STATE.current_procs.pop(qid, None)
            if cancelled:
                n = cleanup_temp_files(entry["path"])
                with STATE.lock:
                    entry["file"] = f"Cancelled · cleaned {n} temp files" if n else "Cancelled"
            elif entry["status"] == "done" and entry.get("cover") and entry.get("folder"):
                # auto-save cover.jpg into the album folder (skips if it exists)
                save_album_cover(
                    entry["cover"],
                    album_dir(Path(entry["path"]), entry.get("artist", ""), entry["folder"]),
                )
        except Exception as e:  # noqa: BLE001
            with STATE.lock:
                entry["status"] = "error"
                entry["file"] = str(e)
                STATE.current_procs.pop(qid, None)


def cancel_entry(qid: str) -> bool:
    with STATE.lock:
        entry = next((e for e in STATE.queue if e["id"] == qid), None)
        if not entry:
            return False
        if entry["status"] == "queued":
            entry["status"] = "cancelled"
            return True
        if entry["status"] == "downloading":
            entry["status"] = "cancelling"
            _terminate(entry["id"])
            return True
    return False


def cancel_all() -> None:
    with STATE.lock:
        for e in STATE.queue:
            if e["status"] == "queued":
                e["status"] = "cancelled"
            elif e["status"] == "downloading":
                e["status"] = "cancelling"
                _terminate(e["id"])


def _terminate(qid: str) -> None:
    """Caller must hold STATE.lock."""
    proc = STATE.current_procs.get(qid)
    if proc:
        try:
            proc.terminate()
        except Exception:  # noqa: BLE001
            pass


def clear_finished() -> None:
    with STATE.lock:
        STATE.queue = [
            e for e in STATE.queue
            if e["status"] in ("queued", "downloading", "cancelling")
        ]


def cleanup_temp_files(base: str) -> int:
    """
    Remove leftover NamedTemporaryFile artifacts from interrupted downloads.
    tiddl writes to a temp file named like 'tmpXXXXXXXX' (no extension) in the
    album folder, then moves it into place — a killed download leaves it behind.
    """
    p = Path(base)
    if not p.is_dir():
        return 0
    removed = 0
    for f in p.rglob("tmp*"):
        try:
            if f.is_file() and f.suffix == "" and re.fullmatch(r"tmp\w+", f.name):
                f.unlink()
                removed += 1
        except OSError:
            pass
    return removed


# ---------------------------------------------------------------------------
# HTTP handler
# ---------------------------------------------------------------------------
class Handler(BaseHTTPRequestHandler):
    def log_message(self, *args):  # silence default logging
        pass

    def _send_json(self, obj, code=200):
        body = json.dumps(obj).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _send_html(self, html: str):
        body = html.encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _read_body(self) -> dict:
        length = int(self.headers.get("Content-Length", 0))
        if not length:
            return {}
        try:
            return json.loads(self.rfile.read(length).decode("utf-8"))
        except json.JSONDecodeError:
            return {}

    # -- GET ---------------------------------------------------------------
    def do_GET(self):
        parsed = urlparse(self.path)
        route = parsed.path
        qs = parse_qs(parsed.query)

        try:
            # SPA fallback: serve the page for any non-API route (e.g. /artist/1502)
            if not route.startswith("/api/"):
                return self._send_html(PAGE)

            if route == "/api/status":
                auth = load_auth_data()
                return self._send_json({
                    "logged_in": bool(auth.token),
                    "user_id": auth.user_id,
                    "country": auth.country_code,
                    "download_path": STATE.download_path,
                    "quality": STATE.quality,
                    "qualities": QUALITIES,
                    "atmos": STATE.atmos,
                    "atmos_filters": ATMOS_FILTERS,
                    "overwrite": STATE.overwrite,
                    "concurrency": STATE.concurrency,
                    "max_concurrency": MAX_CONCURRENCY,
                    "threads": STATE.threads,
                    "max_threads": MAX_THREADS,
                })

            if route == "/api/login/status":
                return self._send_json(dict(STATE.login))

            if route == "/api/search":
                q = (qs.get("q", [""])[0]).strip()
                if not q:
                    return self._send_json({"artists": []})
                api = build_api()
                result = api.get_search(q)
                artists = [{
                    "id": a.id, "name": a.name,
                    "picture": a.picture, "popularity": a.popularity,
                } for a in result.artists.items]
                return self._send_json({"artists": artists})

            if route == "/api/artist":
                # NOTE: api.get_artist() rejects results missing the `type` field,
                # so we rely on name/picture/popularity passed from the search hit.
                aid = qs.get("id", [""])[0]
                name = qs.get("name", [""])[0]
                picture = qs.get("picture", [""])[0] or None
                pop = qs.get("pop", [""])[0]
                base = Path(STATE.download_path)
                try:
                    api = build_api()
                    raw = []  # (album, folder_artist_name, filt)
                    for filt in ("ALBUMS", "EPSANDSINGLES"):
                        offset = 0
                        while True:
                            page = api.get_artist_albums(
                                artist_id=aid, offset=offset, filter=filt, limit=50)
                            for alb in page.items:
                                folder_name = alb.artist.name if alb.artist else name
                                if not name and alb.artist:
                                    name = alb.artist.name
                                raw.append((alb, folder_name, filt))
                            offset += page.limit
                            if offset >= page.totalNumberOfItems:
                                break
                    # disambiguate albums that share an identical title with [id]
                    from collections import Counter
                    title_counts = Counter(a.title.lower() for a, _, _ in raw)
                    real_counts = load_album_counts()  # album_id -> real track count
                    albums, singles = [], []
                    for alb, folder_name, filt in raw:
                        dup = title_counts[alb.title.lower()] > 1
                        folder_title = f"{alb.title} [{alb.id}]" if dup else None
                        st = album_status(base, folder_name, alb, folder_title,
                                          total_override=real_counts.get(str(alb.id)))
                        st["dup"] = dup
                        st["folder_artist"] = folder_name  # for offline recompute
                        (albums if filt == "ALBUMS" else singles).append(st)
                    if not picture and name:
                        meta = load_registry().get(clean_segment(name))
                        if meta:
                            picture = meta.get("picture")
                    if name:
                        register_artist(aid, name, picture)
                    response = {
                        "artist": {
                            "id": aid, "name": name or "Unknown", "picture": picture,
                            "popularity": int(pop) if pop.isdigit() else None,
                        },
                        "albums": albums, "singles": singles,
                    }
                    save_artist_cache(aid, response)
                    return self._send_json(response)
                except Exception as e:  # noqa: BLE001 — fall back to offline cache
                    cached = load_artist_cache(aid)
                    if not cached:
                        raise
                    for alb in cached.get("albums", []) + cached.get("singles", []):
                        recompute_album_state(alb, base)
                    cached["offline"] = True
                    cached["offline_reason"] = str(e)
                    return self._send_json(cached)

            if route == "/api/album":
                aid = qs.get("id", [""])[0]
                artist = qs.get("artist", [""])[0]
                title = qs.get("title", [""])[0]
                api = build_api()
                # scan the album folder once; map cleaned stem -> file path
                d = album_dir(Path(STATE.download_path), artist, title)
                existing: dict[str, Path] = {}
                if d.is_dir():
                    for p in d.iterdir():
                        if p.is_file() and p.suffix.lower() in AUDIO_EXTENSIONS:
                            existing[clean_segment(p.stem).lower()] = p
                tracks = []
                offset = 0
                while True:
                    page = api.get_album_items(album_id=aid, offset=offset)
                    for it in page.items:
                        item = it.item
                        version = getattr(item, "version", None) or ""
                        display = f"{item.title} ({version})" if version else item.title
                        cleaned_tv = clean_segment(display).lower()
                        cleaned_t = clean_segment(item.title).lower()
                        # match the version-aware name; fall back to plain title
                        # only for versionless tracks (old downloads).
                        path = existing.get(cleaned_tv) or (
                            existing.get(cleaned_t) if not version else None)
                        finfo = file_audio_info(path) if path else {}
                        tags = getattr(getattr(item, "mediaMetadata", None), "tags", [])
                        tracks.append({
                            "number": getattr(item, "trackNumber", 0),
                            "title": item.title,
                            "version": version,
                            "duration": item.duration,
                            "artists": ", ".join(a.name for a in (item.artists or [])),
                            "type": it.type,
                            "downloaded": path is not None,
                            "quality": quality_label(getattr(item, "audioQuality", ""), tags),
                            "size": finfo.get("size"),
                            "bits": finfo.get("bits"),
                            "sampleRate": finfo.get("sampleRate"),
                        })
                    offset += page.limit
                    if offset >= page.totalNumberOfItems:
                        break
                # remember the real track count so the artist card can show the
                # correct "downloaded" status (Tidal's numberOfTracks may be higher).
                save_album_count(aid, len(tracks))
                return self._send_json({"id": aid, "title": title, "tracks": tracks})

            if route == "/api/library":
                base = Path(STATE.download_path)
                reg = load_registry()
                reg_lower = {k.lower(): v for k, v in reg.items()}
                artists = []
                if base.is_dir():
                    for d in sorted(base.iterdir(), key=lambda p: p.name.lower()):
                        if not d.is_dir():
                            continue
                        albums = [s for s in d.iterdir() if s.is_dir()]
                        tracks = sum(
                            1 for p in d.rglob("*")
                            if p.is_file() and p.suffix.lower() in AUDIO_EXTENSIONS
                        )
                        if tracks == 0 and not albums:
                            continue
                        meta = reg.get(d.name) or reg_lower.get(d.name.lower(), {})
                        artists.append({
                            "name": d.name,
                            "albums": len(albums),
                            "tracks": tracks,
                            "id": meta.get("id"),
                            "picture": meta.get("picture"),
                        })
                return self._send_json({"artists": artists, "path": str(base)})

            if route == "/api/covers-all/status":
                with STATE.lock:
                    return self._send_json(dict(STATE.cover_job))

            if route == "/api/queue":
                with STATE.lock:
                    items = [
                        {**{k: e[k] for k in ("id", "title", "kind", "artist", "status",
                                              "file", "track_total", "track_done")},
                         "log": e.get("log", [])}
                        for e in STATE.queue
                    ]
                active = sum(1 for e in items if e["status"] in ("queued", "downloading", "cancelling"))
                return self._send_json({"queue": items, "active": active})

            return self._send_json({"error": "not found"}, 404)

        except RuntimeError as e:
            return self._send_json({"error": str(e), "need_login": True}, 401)
        except Exception as e:  # noqa: BLE001
            return self._send_json({"error": str(e)}, 500)

    # -- POST --------------------------------------------------------------
    def do_POST(self):
        route = urlparse(self.path).path
        body = self._read_body()

        try:
            if route == "/api/login":
                return self._send_json(start_login())

            if route == "/api/logout":
                save_auth_data(AuthData())
                STATE.login = {"active": False, "url": "", "message": "", "done": False}
                return self._send_json({"ok": True})

            if route == "/api/pkce/start":
                return self._send_json({"url": pkce_start()})

            if route == "/api/pkce/finish":
                return self._send_json(pkce_finish(body.get("url", "")))

            if route == "/api/config":
                if "download_path" in body:
                    STATE.download_path = body["download_path"]
                if "quality" in body and body["quality"] in QUALITIES:
                    STATE.quality = body["quality"]
                if "atmos" in body and body["atmos"] in ATMOS_FILTERS:
                    STATE.atmos = body["atmos"]
                if "overwrite" in body:
                    STATE.overwrite = bool(body["overwrite"])
                if "concurrency" in body:
                    try:
                        STATE.concurrency = min(max(int(body["concurrency"]), 1), MAX_CONCURRENCY)
                    except (ValueError, TypeError):
                        pass
                if "threads" in body:
                    try:
                        STATE.threads = min(max(int(body["threads"]), 1), MAX_THREADS)
                    except (ValueError, TypeError):
                        pass
                save_settings(STATE.download_path, STATE.quality, STATE.atmos,
                              STATE.overwrite, STATE.concurrency, STATE.threads)
                ensure_workers()  # spawn more workers if concurrency was raised mid-queue
                return self._send_json({
                    "download_path": STATE.download_path, "quality": STATE.quality,
                    "atmos": STATE.atmos, "overwrite": STATE.overwrite,
                    "concurrency": STATE.concurrency, "threads": STATE.threads})

            if route == "/api/download":
                items = body.get("items") or []
                # backward-compat: accept plain resource strings too
                if not items and body.get("resources"):
                    items = [{"resource": r} for r in body["resources"]]
                if not items:
                    return self._send_json({"error": "no resources"}, 400)
                path = body.get("path") or STATE.download_path
                quality = body.get("quality") or STATE.quality
                STATE.download_path = path
                STATE.quality = quality
                save_settings(path, quality, STATE.atmos, STATE.overwrite,
                              STATE.concurrency, STATE.threads)
                ids = enqueue(items, path, quality)
                return self._send_json({"queued": ids})

            if route == "/api/cancel":
                if body.get("all"):
                    cancel_all()
                    return self._send_json({"ok": True})
                qid = body.get("id", "")
                return self._send_json({"ok": cancel_entry(qid)})

            if route == "/api/queue/clear":
                clear_finished()
                return self._send_json({"ok": True})

            if route == "/api/covers":
                artist = body.get("artist", "")
                items = body.get("items") or []
                overwrite = bool(body.get("overwrite", False))
                base = Path(STATE.download_path)
                from collections import Counter
                res = Counter()
                for it in items:
                    d = album_dir(base, artist, it.get("folder", ""))
                    res[save_album_cover(it.get("cover", ""), d, overwrite=overwrite)] += 1
                return self._send_json({
                    "saved": res["saved"], "exists": res["exists"],
                    "missing": res["missing"], "nocover": res["nocover"],
                    "failed": res["failed"],
                })

            if route == "/api/covers-all":
                with STATE.lock:
                    already = STATE.cover_job["running"]
                    if not already:
                        STATE.cover_job["running"] = True  # set now so polling sees it
                if not already:
                    threading.Thread(target=run_covers_all, daemon=True).start()
                return self._send_json({"started": True})

            if route == "/api/open-folder":
                base = Path(STATE.download_path)
                artist = body.get("artist", "")
                target = base
                if artist:
                    d = base / clean_segment(artist)
                    if d.is_dir():
                        target = d
                if not target.exists():
                    return self._send_json({"ok": False, "error": "Folder does not exist yet"})
                return self._send_json({"ok": open_folder(target), "path": str(target)})

            return self._send_json({"error": "not found"}, 404)

        except Exception as e:  # noqa: BLE001
            return self._send_json({"error": str(e)}, 500)


# ---------------------------------------------------------------------------
# Frontend (single page) — Monochrome-inspired
# ---------------------------------------------------------------------------
PAGE = r"""<!doctype html>
<html lang="vi">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>tiddl</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700&display=swap" rel="stylesheet">
<style>
  :root {
    --background:#0a0a0a; --foreground:#f5f5f5; --card:#141414; --secondary:#1f1f1f;
    --muted-foreground:#a0a0a0; --border:#2a2a2a; --primary:#f5f5f5; --primary-fg:#0a0a0a;
    --radius:8px; --radius-full:9999px; --shadow-lg:0 10px 15px -3px rgba(0,0,0,.4);
    --shadow-xl:0 20px 25px -5px rgba(0,0,0,.5); --ease:cubic-bezier(.34,1.56,.64,1);
    --ok:#10b981; --warn:#f59e0b; --font:'Inter',system-ui,-apple-system,'Segoe UI',Roboto,sans-serif;
  }
  * { box-sizing:border-box; margin:0; padding:0; font-family:var(--font); }
  html,body { height:100%; }
  body { background:var(--background); color:var(--foreground); overflow:hidden;
    -webkit-font-smoothing:antialiased; }
  a { color:inherit; text-decoration:none; }

  .app { display:grid; grid-template-columns:230px 1fr; height:100vh; }

  /* Sidebar */
  .sidebar { border-right:1px solid var(--border); padding:18px 16px; display:flex;
    flex-direction:column; gap:18px; overflow-y:auto; }
  .brand { display:flex; align-items:center; gap:8px; font-weight:700; font-size:20px; }
  .brand .dot { width:14px; height:14px; border-radius:50%; background:var(--foreground); }
  .nav { display:flex; flex-direction:column; gap:4px; }
  .navitem { padding:9px 11px; border-radius:var(--radius); color:var(--muted-foreground);
    cursor:pointer; font-size:13px; font-weight:500; transition:background .15s, color .15s; }
  .navitem:hover { background:var(--secondary); color:var(--foreground); }
  .navitem.active { background:var(--primary); color:var(--primary-fg); }
  .auth { background:var(--secondary); border:1px solid var(--border); border-radius:var(--radius);
    padding:12px; font-size:13px; }
  .auth .state { display:flex; align-items:center; gap:8px; margin-bottom:8px; }
  .auth .led { width:9px; height:9px; border-radius:50%; background:var(--warn); flex:0 0 auto; }
  .auth.ok .led { background:var(--ok); }
  .field { display:flex; flex-direction:column; gap:6px; font-size:12px; color:var(--muted-foreground); }
  input, select { width:100%; background:var(--background); border:1px solid var(--border);
    color:var(--foreground); border-radius:var(--radius); padding:9px 11px; font-size:13px; outline:none; }
  input:focus, select:focus { border-color:var(--primary); }
  button { cursor:pointer; border:none; border-radius:var(--radius-full); font-weight:600;
    transition:transform .15s var(--ease), background .15s, opacity .15s; font-size:13px; }
  .btn { background:var(--primary); color:var(--primary-fg); padding:10px 16px; }
  .btn:hover { transform:scale(1.03); }
  .btn.ghost { background:var(--secondary); color:var(--foreground); }
  .btn.block { width:100%; }
  .btn.sm { padding:7px 12px; font-size:12px; }
  .muted { color:var(--muted-foreground); }
  .loginbox { font-size:13px; }
  .loginbox a { color:var(--foreground); text-decoration:underline; }

  /* Main */
  .main { overflow-y:auto; position:relative; }
  .page-bg { position:absolute; top:0; left:0; right:0; height:420px; z-index:0;
    background-size:cover; background-position:center 25%; opacity:0;
    transition:opacity .6s ease; filter:blur(50px) brightness(.45);
    mask-image:linear-gradient(to bottom, #000 0%, rgba(0,0,0,.7) 45%, transparent 100%); }
  .page-bg.show { opacity:1; }
  .content { position:relative; z-index:1; padding:22px 30px 120px; max-width:1280px; margin:0 auto; }

  .topbar { display:flex; align-items:center; gap:14px; margin-bottom:26px; position:sticky; top:0;
    z-index:5; padding:14px 0; }
  .searchwrap { position:relative; flex:1; max-width:520px; margin-left:auto; }
  .searchwrap svg { position:absolute; left:12px; top:50%; transform:translateY(-50%);
    color:var(--muted-foreground); }
  .searchwrap input { padding-left:38px; border-radius:var(--radius-full); background:var(--card); }

  .section-title { font-size:24px; font-weight:700; margin:28px 0 14px; }
  .grid { display:grid; grid-template-columns:repeat(auto-fill,minmax(170px,1fr)); gap:18px; }

  .card { background:var(--card); border:1px solid transparent; border-radius:var(--radius);
    padding:12px; cursor:pointer; transition:transform .3s var(--ease), background .3s, box-shadow .3s; }
  .card:hover { transform:translateY(-6px); background:var(--secondary);
    box-shadow:var(--shadow-lg); border-color:var(--border); }
  .cover { position:relative; aspect-ratio:1; border-radius:var(--radius); overflow:hidden;
    background:var(--secondary); box-shadow:0 4px 6px -1px rgba(0,0,0,.3); }
  .cover img { width:100%; height:100%; object-fit:cover; transition:transform .5s; }
  .card:hover .cover img { transform:scale(1.05); }
  .card.artist .cover, .card.artist .cover img { border-radius:var(--radius-full); }
  .badge { position:absolute; left:8px; top:8px; font-size:11px; font-weight:600; padding:3px 8px;
    border-radius:var(--radius-full); background:rgba(0,0,0,.6); backdrop-filter:blur(6px); }
  .badge.done { color:#34d399; } .badge.partial { color:#fbbf24; } .badge.none { color:#cbd5e1; }
  .card .cmpbtn { position:absolute; right:8px; top:8px; opacity:0; transform:scale(.85);
    background:rgba(0,0,0,.55); backdrop-filter:blur(6px); color:#fff; width:32px; height:32px;
    border-radius:50%; display:flex; align-items:center; justify-content:center; font-size:15px;
    transition:opacity .2s, transform .2s var(--ease); }
  .card:hover .cmpbtn { opacity:1; transform:scale(1); }
  .card.sel { outline:2px solid var(--primary); outline-offset:2px; }
  .card.sel .cmpbtn { opacity:1; transform:scale(1); background:var(--primary); color:var(--primary-fg); }
  /* compare tray + split view */
  .cmptray { position:fixed; left:18px; bottom:18px; z-index:60; display:none; gap:10px; align-items:center;
    background:color-mix(in srgb,var(--card) 92%,transparent); backdrop-filter:blur(20px);
    border:1px solid var(--border); border-radius:12px; padding:10px 14px; box-shadow:var(--shadow-xl); }
  .cmptray.show { display:flex; }
  .cmptray .ci { font-size:13px; color:var(--muted-foreground); max-width:280px; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }
  .cmp-head { display:flex; align-items:center; gap:12px; margin-bottom:16px; }
  .cmp-grid { display:grid; grid-template-columns:1fr 1fr; gap:18px; align-items:start; }
  @media (max-width:860px){ .cmp-grid { grid-template-columns:1fr; } }
  .cmp-col { background:var(--card); border:1px solid var(--border); border-radius:12px; overflow:hidden; }
  .cmp-colhead { display:flex; gap:12px; padding:14px; border-bottom:1px solid var(--border); align-items:center; }
  .cmp-colhead img { width:64px; height:64px; border-radius:8px; object-fit:cover; background:var(--secondary); flex:0 0 auto; }
  .cmp-colhead .h3 { font-weight:700; }
  .cmp-sum { padding:10px 14px; font-size:13px; color:var(--muted-foreground); border-bottom:1px solid var(--border); }
  .cmp-rows .trow.uniq { background:rgba(52,211,153,.12); box-shadow:inset 3px 0 #34d399; }
  .card .dlbtn { position:absolute; right:8px; bottom:8px; opacity:0; transform:scale(.85);
    background:var(--primary); color:var(--primary-fg); width:38px; height:38px; border-radius:50%;
    display:flex; align-items:center; justify-content:center; box-shadow:var(--shadow-lg);
    transition:opacity .2s, transform .2s var(--ease); }
  .card:hover .dlbtn { opacity:1; transform:scale(1); }
  .c-title { font-weight:600; margin-top:10px; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }
  .c-sub { font-size:12px; color:var(--muted-foreground); margin-top:2px; white-space:nowrap;
    overflow:hidden; text-overflow:ellipsis; }

  /* Artist header */
  .artisthead { display:flex; gap:26px; align-items:flex-end; padding-top:30px; margin-bottom:8px; }
  .artisthead .ava { width:170px; height:170px; border-radius:50%; object-fit:cover; flex:0 0 auto;
    box-shadow:var(--shadow-xl); background:var(--secondary); }
  .artisthead h1 { font-size:52px; font-weight:700; line-height:1.05; }
  .artisthead .meta { color:var(--muted-foreground); margin-top:10px; font-size:14px; }
  .artisthead .actions { display:flex; gap:12px; flex-wrap:wrap; margin-top:18px; }

  /* Download queue dock — floating panel */
  .dock { position:fixed; left:50%; transform:translateX(-50%) translateY(140%);
    bottom:18px; width:min(820px,94%); background:color-mix(in srgb, var(--card) 92%, transparent);
    backdrop-filter:blur(20px); border:1px solid var(--border); border-radius:14px;
    box-shadow:var(--shadow-xl); z-index:50; transition:transform .4s var(--ease); overflow:hidden; }
  .dock.show { transform:translateX(-50%) translateY(0); }
  .dock-head { display:flex; align-items:center; gap:10px; padding:12px 16px; border-bottom:1px solid var(--border); }
  .dock-head b { font-weight:600; }
  .dock-list { max-height:300px; overflow-y:auto; padding:6px; }
  .dock-list.collapsed { display:none; }
  .qrow { display:grid; grid-template-columns:26px 1fr auto; gap:10px; align-items:center;
    padding:8px 10px; border-radius:8px; }
  .qrow:hover { background:var(--secondary); }
  .qst { text-align:center; }
  .qst.downloading, .qst.cancelling { animation:pulse 1.2s infinite; }
  .qst.done { color:#34d399; } .qst.error { color:#f87171; } .qst.cancelled { color:#888; }
  @keyframes pulse { 0%,100%{opacity:1} 50%{opacity:.4} }
  .qinfo { min-width:0; }
  .qt { white-space:nowrap; overflow:hidden; text-overflow:ellipsis; font-weight:500; }
  .qt .qk { color:var(--muted-foreground); font-weight:400; font-size:12px; }
  .qf { font-size:12px; color:var(--muted-foreground); white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }
  .qf.err { color:#f87171; }
  .qcancel { background:var(--secondary); width:28px; height:28px; border-radius:50%; color:var(--foreground); }
  .qcancel:hover { background:#7f1d1d; color:#fff; }
  .hidden { display:none; }
  .empty { color:var(--muted-foreground); padding:40px 0; text-align:center; }

  /* Modal */
  .overlay { position:fixed; inset:0; background:rgba(0,0,0,.6); backdrop-filter:blur(4px);
    display:none; align-items:center; justify-content:center; z-index:100; padding:20px; }
  .overlay.show { display:flex; animation:fade .2s ease; }
  @keyframes fade { from{opacity:0} to{opacity:1} }
  .modal { background:var(--card); border:1px solid var(--border); border-radius:14px;
    width:min(620px,100%); max-height:84vh; display:flex; flex-direction:column;
    box-shadow:var(--shadow-xl); overflow:hidden; animation:pop .25s var(--ease); }
  @keyframes pop { from{transform:scale(.95);opacity:0} to{transform:scale(1);opacity:1} }
  .modal-head { display:flex; gap:16px; align-items:center; padding:18px; border-bottom:1px solid var(--border); }
  .modal-head img { width:74px; height:74px; border-radius:8px; object-fit:cover; background:var(--secondary); flex:0 0 auto; }
  .modal-head .mt { flex:1; min-width:0; }
  .modal-head h3 { font-size:20px; font-weight:700; }
  .modal-head .ms { color:var(--muted-foreground); font-size:13px; margin-top:4px; }
  .modal-head .x { background:var(--secondary); width:34px; height:34px; border-radius:50%;
    color:var(--foreground); font-size:18px; flex:0 0 auto; }
  .tracklist { overflow-y:auto; padding:8px; }
  .trow { display:grid; grid-template-columns:34px 1fr auto auto; gap:12px; align-items:center;
    padding:9px 12px; border-radius:8px; }
  .trow:hover { background:var(--secondary); }
  .trow .num { color:var(--muted-foreground); text-align:right; font-size:13px; }
  .trow .tt { min-width:0; }
  .trow .tt .nm { white-space:nowrap; overflow:hidden; text-overflow:ellipsis; font-weight:500; }
  .trow .tt .nm .ver { color:var(--muted-foreground); font-weight:400; }
  .trow .tt .ar { color:var(--muted-foreground); font-size:12px; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; }
  .trow .dur { color:var(--muted-foreground); font-size:13px; }
  .trow .dl { font-size:12px; color:var(--muted-foreground); }
  .trow .dl.done { color:#34d399; }
  .modal-foot { padding:14px 18px; border-top:1px solid var(--border); display:flex; gap:10px; justify-content:flex-end; }
  ::-webkit-scrollbar { width:10px; height:10px; }
  ::-webkit-scrollbar-thumb { background:#333; border-radius:6px; }
</style>
</head>
<body>
<div class="app">
  <aside class="sidebar">
    <div class="brand"><span class="dot"></span> tiddl</div>

    <nav class="nav">
      <a class="navitem active" id="navSearch" onclick="goSearch()">🔎 Search</a>
      <a class="navitem" id="navLib" onclick="openLibrary()">📁 Downloaded artists</a>
    </nav>

    <div id="auth" class="auth">
      <div class="state"><span class="led"></span><span id="authText">Checking...</span></div>
      <button id="loginBtn" class="btn block sm hidden">Log in to Tidal</button>
      <button id="reloginBtn" class="btn ghost block sm hidden" onclick="relogin()" style="margin-top:6px">Log in again (Hi-Res)</button>
    </div>

    <div id="loginBox" class="loginbox hidden">
      <p class="muted" id="loginMsg"></p>
      <a id="loginLink" target="_blank" class="btn block sm" style="margin-bottom:8px"></a>
      <input id="pkceCode" placeholder="② Paste the URL with the code..." style="margin-bottom:6px">
      <button class="btn block sm" onclick="pkceFinish()">③ Finish login</button>
    </div>

    <div class="field">
      <label>Download folder</label>
      <div style="display:flex; gap:6px">
        <input id="path" placeholder="path..." style="flex:1; min-width:0">
        <button class="btn ghost sm" onclick="openFolder()" title="Open download folder">📁</button>
      </div>
    </div>
    <div class="field">
      <label>Quality</label>
      <select id="quality"></select>
    </div>
    <div class="field">
      <label>Dolby Atmos</label>
      <select id="atmos"></select>
    </div>
    <div class="field">
      <label>Parallel downloads (albums at once)</label>
      <select id="concurrency"></select>
    </div>
    <div class="field">
      <label>Threads per album (tracks at once)</label>
      <select id="threads"></select>
    </div>
    <label style="display:flex; align-items:center; gap:8px; font-size:13px; cursor:pointer; color:var(--foreground)">
      <input type="checkbox" id="overwrite" style="width:auto"> Overwrite (don't skip existing files)
    </label>
    <button id="saveCfg" class="btn ghost block sm">Save settings</button>
    <div class="muted" style="font-size:11px; margin-top:auto; line-height:1.5;">
      Re-downloading skips existing tracks.<br>UI inspired by Monochrome.
    </div>
  </aside>

  <main class="main">
    <div class="page-bg" id="pageBg"></div>
    <div class="content">
      <div class="topbar">
        <div class="searchwrap">
          <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><circle cx="11" cy="11" r="8"/><path d="m21 21-4.3-4.3"/></svg>
          <input id="search" placeholder="Search artist...">
        </div>
      </div>
      <div id="view"><div class="empty">Search for an artist to begin.</div></div>
    </div>
  </main>
</div>

<div class="overlay" id="overlay" onclick="if(event.target===this)closeModal()">
  <div class="modal">
    <div class="modal-head">
      <img id="mCover" src="">
      <div class="mt"><h3 id="mTitle"></h3><div class="ms" id="mSub"></div></div>
      <button class="x" onclick="closeModal()">✕</button>
    </div>
    <div class="tracklist" id="mTracks"></div>
    <div class="modal-foot">
      <button class="btn ghost" onclick="closeModal()">Close</button>
      <button class="btn" id="mDl">Download this</button>
    </div>
  </div>
</div>

<div class="cmptray" id="cmptray">
  <span class="ci" id="cmptrayItems"></span>
  <button class="btn sm" id="cmpGo" onclick="openCompare()">Compare ⇄</button>
  <button class="btn ghost sm" onclick="clearCompare()">Clear</button>
</div>

<div class="dock" id="dock">
  <div class="dock-head">
    <b>Download queue</b><span id="dockCount" class="muted"></span>
    <div style="margin-left:auto; display:flex; gap:8px; align-items:center">
      <button class="btn ghost sm" onclick="clearDone()">Clear finished</button>
      <button class="btn ghost sm" onclick="cancelAll()">Cancel all</button>
      <button class="x" id="dockToggle" onclick="toggleDock()">▾</button>
    </div>
  </div>
  <div class="dock-list" id="dockList"></div>
</div>

<script>
const $ = s => document.querySelector(s);
const img = (id, size=320) => id ? `https://resources.tidal.com/images/${id.replaceAll('-','/')}/${size}x${size}.jpg` : '';
const DL_ICON = '<svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2"><path d="M12 3v12m0 0 4-4m-4 4-4-4"/><path d="M5 21h14"/></svg>';
let CURRENT_ARTIST = null;

async function api(path, opts) {
  const r = await fetch(path, opts);
  const data = await r.json().catch(()=>({}));
  if (r.status === 401 && data.need_login) showLogin();
  return data;
}

async function refreshStatus() {
  const s = await fetch('/api/status').then(r=>r.json());
  const box = $('#auth'), txt = $('#authText');
  if (s.logged_in) { box.classList.add('ok'); txt.textContent = `Logged in · user ${s.user_id}`; $('#loginBtn').classList.add('hidden'); $('#reloginBtn').classList.remove('hidden'); }
  else { box.classList.remove('ok'); txt.textContent = 'Not logged in'; $('#loginBtn').classList.remove('hidden'); $('#reloginBtn').classList.add('hidden'); }
  $('#path').value = s.download_path;
  const sel = $('#quality'); sel.innerHTML='';
  s.qualities.forEach(q => { const o=document.createElement('option'); o.value=q; o.textContent=q.toUpperCase(); if(q===s.quality)o.selected=true; sel.appendChild(o); });
  const asel = $('#atmos'); asel.innerHTML='';
  const aLabels = {none:'Skip', allow:'Allow', only:'Atmos only'};
  (s.atmos_filters||['none','allow','only']).forEach(a => { const o=document.createElement('option'); o.value=a; o.textContent=aLabels[a]||a; if(a===s.atmos)o.selected=true; asel.appendChild(o); });
  $('#overwrite').checked = !!s.overwrite;
  const csel = $('#concurrency'); csel.innerHTML='';
  for (let i=1; i<=(s.max_concurrency||4); i++){ const o=document.createElement('option'); o.value=i; o.textContent=i+(i===1?' (sequential)':''); if(i===s.concurrency)o.selected=true; csel.appendChild(o); }
  const tsel = $('#threads'); tsel.innerHTML='';
  [1,2,4,6,8,12,16].filter(n=>n<=(s.max_threads||16)).forEach(n=>{ const o=document.createElement('option'); o.value=n; o.textContent=n; if(n===s.threads)o.selected=true; tsel.appendChild(o); });
  if (!Array.from(tsel.options).some(o=>o.selected)) { const o=document.createElement('option'); o.value=s.threads; o.textContent=s.threads; o.selected=true; tsel.appendChild(o); }
}

$('#saveCfg').onclick = async () => {
  await api('/api/config', {method:'POST', headers:{'Content-Type':'application/json'},
    body: JSON.stringify({download_path: $('#path').value, quality: $('#quality').value, atmos: $('#atmos').value, overwrite: $('#overwrite').checked, concurrency: parseInt($('#concurrency').value), threads: parseInt($('#threads').value)})});
  const b=$('#saveCfg'); b.textContent='Saved ✓'; setTimeout(()=>b.textContent='Save settings', 1200);
};

// ---- login (PKCE Hi-Res) ----
$('#loginBtn').onclick = pkceLogin;
async function relogin() {
  if (!confirm('Log out of the current session and log in again?\n\nYou will need to log in to Tidal from scratch. Click Cancel to keep the current session.')) return;
  await fetch('/api/logout', {method:'POST'});
  await refreshStatus();
  pkceLogin();
}
async function pkceLogin() {
  const box = $('#loginBox'); box.classList.remove('hidden');
  $('#loginMsg').textContent = 'Click ①, log in, copy the redirect URL (with the code), paste into ② then click ③.';
  const r = await fetch('/api/pkce/start', {method:'POST'}).then(r=>r.json());
  const link = $('#loginLink');
  link.href = r.url; link.textContent = '① Open Tidal login page ↗';
  try { window.open(r.url, '_blank'); } catch (e) {}
}
async function pkceFinish() {
  const url = $('#pkceCode').value.trim();
  if (!url) { $('#loginMsg').textContent = 'Paste the URL with the code into field ②.'; return; }
  $('#loginMsg').textContent = 'Exchanging token...';
  const r = await fetch('/api/pkce/finish', {method:'POST', headers:{'Content-Type':'application/json'},
    body: JSON.stringify({url})}).then(r=>r.json());
  if (r.ok) {
    $('#loginMsg').textContent = `Logged in! (user ${r.user_id})`;
    $('#pkceCode').value = '';
    await refreshStatus();
    setTimeout(()=>$('#loginBox').classList.add('hidden'), 1800);
  } else {
    $('#loginMsg').textContent = 'Error: ' + (r.error || 'unknown');
  }
}

// ---- nav ----
function setNav(which) {
  $('#navSearch').classList.toggle('active', which==='search');
  $('#navLib').classList.toggle('active', which==='lib');
}
function goSearch() {
  setNav('search'); setBg(null);
  if (location.pathname !== '/') history.pushState({}, '', '/');
  const q = $('#search').value.trim();
  if (q) doSearch(q); else show('<div class="empty">Search for an artist to begin.</div>');
}

// path routing — e.g. /artist/1502 opens the artist directly (Tidal-style)
function route() {
  const m = location.pathname.match(/^\/artist\/(\d+)/);
  if (m) { openArtist(m[1], false); return; }
  setNav('search'); setBg(null);
  const q = $('#search').value.trim();
  if (q) doSearch(q); else show('<div class="empty">Search for an artist to begin.</div>');
}

// ---- library (downloaded artists) ----
async function openLibrary() {
  setNav('lib'); setBg(null);
  show('<div class="empty">Scanning download folder...</div>');
  const data = await fetch('/api/library').then(r=>r.json());
  const list = data.artists || [];
  const cards = list.map(a => {
    const cover = a.picture
      ? `<img src="${img(a.picture)}" onerror="this.style.visibility='hidden'">`
      : `<div style="width:100%;height:100%;display:flex;align-items:center;justify-content:center;font-size:42px;font-weight:700;color:var(--muted-foreground)">${esc((a.name[0]||'?').toUpperCase())}</div>`;
    const sub = a.id ? `id: ${a.id} · ${a.tracks} tracks` : `${a.albums} folders · ${a.tracks} tracks`;
    const onclick = a.id
      ? `openArtist(${attr(a)})`
      : `libOpen(${attr(a.name)})`;
    const title = a.id ? `Open artist ${esc(a.name)}` : `Search '${esc(a.name)}' on Tidal (no id yet)`;
    return `
    <div class="card artist" onclick='${onclick}' title="${title}">
      <div class="cover">${cover}</div>
      <div class="c-title">${esc(a.name)}</div>
      <div class="c-sub">${sub}</div>
    </div>`;
  }).join('');
  show(`<div class="section-title">Downloaded artists <span class="muted" style="font-size:15px">(${list.length})</span></div>
    <div style="display:flex; align-items:center; gap:12px; margin-bottom:14px; flex-wrap:wrap">
      <span class="muted">Scanned from: ${esc(data.path)}</span>
      <button class="btn ghost sm" id="coverAllBtn" onclick="downloadAllCovers()">🖼️ Download all covers</button>
    </div>
    <div class="grid">${cards || '<div class="empty">No artists in the download folder yet.</div>'}</div>`);
}
function libOpen(name) {
  $('#search').value = name; setNav('search'); doSearch(name);
}

// ---- search ----
let searchTimer = null;
$('#search').addEventListener('input', e => {
  clearTimeout(searchTimer);
  const q = e.target.value.trim();
  setNav('search');
  searchTimer = setTimeout(()=> q ? doSearch(q) : null, 400);
});
async function doSearch(q) {
  setBg(null);
  const data = await api('/api/search?q='+encodeURIComponent(q));
  if (data.error) return show(`<div class="empty">${esc(data.error)}</div>`);
  const cards = (data.artists||[]).map(a => `
    <div class="card artist" onclick='openArtist(${attr(a)})'>
      <div class="cover"><img src="${img(a.picture)}" onerror="this.style.visibility='hidden'"></div>
      <div class="c-title">${esc(a.name)}</div>
      <div class="c-sub">id: ${a.id}${a.popularity!=null?' · '+a.popularity:''}</div>
    </div>`).join('');
  show(`<div class="section-title">Artists</div><div class="grid">${cards||'<div class="empty">No results.</div>'}</div>`);
}

// ---- artist page ----
async function openArtist(sel, pushUrl=true) {
  const hit = (typeof sel === 'object') ? sel : {id:sel, name:'', picture:'', popularity:''};
  setNav('search');
  show('<div class="empty">Loading...</div>');
  const qs = `id=${hit.id}&name=${encodeURIComponent(hit.name||'')}&picture=${encodeURIComponent(hit.picture||'')}&pop=${hit.popularity??''}`;
  const data = await api('/api/artist?'+qs);
  if (data.error) return show(`<div class="empty">${esc(data.error)}</div>`);
  CURRENT_ARTIST = data.artist;
  const url = '/artist/'+data.artist.id;
  if (pushUrl && location.pathname !== url) history.pushState({}, '', url);
  const a = data.artist;
  setBg(img(a.picture, 1280));
  const grid = (list, kind) => list.map(al => `
    <div class="card" data-album-id="${al.id}" onclick='openAlbum(${attr(al)}, ${attr(kind)})'>
      <div class="cover">
        <img src="${img(al.cover)}" onerror="this.style.visibility='hidden'">
        <span class="badge ${al.state}">${esc(al.statusLabel)}</span>
        <button class="cmpbtn" title="Select to compare" onclick='event.stopPropagation();toggleCompare(${attr(al)}, ${attr(kind)})'>⇄</button>
        <button class="dlbtn" title="Download" onclick='event.stopPropagation();downloadAlbum(${attr(al)}, ${attr(kind)})'>${DL_ICON}</button>
      </div>
      <div class="c-title">${esc(al.title)}</div>
      <div class="c-sub">${kind} · ${al.year||''}</div>
      <div class="c-sub">${al.numberOfTracks} tracks${al.format?' · '+esc(al.format):''}</div>
    </div>`).join('');
  window._albums = data.albums; window._singles = data.singles;
  const offlineBanner = data.offline
    ? `<div style="background:#7c2d12;color:#fff;padding:10px 14px;border-radius:10px;margin-bottom:14px;font-size:13px">📴 Viewing offline (cached data) — can't reach Tidal. The "downloaded" status is still updated from disk.</div>`
    : '';
  show(`
    ${offlineBanner}
    <div class="artisthead">
      <img class="ava" src="${img(a.picture,640)}" onerror="this.style.visibility='hidden'">
      <div>
        <h1>${esc(a.name)}</h1>
        <div class="meta">id: ${a.id} &nbsp;·&nbsp; ${a.popularity??''} popularity &nbsp;·&nbsp; ${data.albums.length} albums · ${data.singles.length} singles</div>
        <div class="actions">
          <button class="btn" onclick='downloadAll("albums", "Album")'>Download all Albums</button>
          <button class="btn ghost" onclick='downloadAll("singles", "Single/EP")'>Download EP & Singles</button>
          <button class="btn ghost" onclick='openFolder(${attr(a.name)})'>📁 Open folder</button>
          <button class="btn ghost" id="coverBtn" onclick='downloadCovers(${attr(a.name)})'>🖼️ Download covers</button>
        </div>
      </div>
    </div>
    <div class="section-title">Albums</div><div class="grid">${grid(data.albums, 'Album')||'<div class="empty">—</div>'}</div>
    <div class="section-title">EP &amp; Singles</div><div class="grid">${grid(data.singles, 'Single/EP')||'<div class="empty">—</div>'}</div>`);
  refreshCompareUI();
}

// ---- album track-list popup ----
function fmtDur(s){ s=Math.round(s||0); const m=Math.floor(s/60), x=String(s%60).padStart(2,'0'); return `${m}:${x}`; }
function fmtSize(b){ if(!b) return ''; const mb=b/1048576; return mb>=1024?(mb/1024).toFixed(2)+' GB':mb.toFixed(1)+' MB'; }
function trackSpecs(t){
  if(!t.downloaded) return '';
  const p=[];
  if(t.bits) p.push(t.bits+'-bit');
  if(t.sampleRate) p.push((t.sampleRate/1000).toFixed(1).replace(/\.0$/,'')+' kHz');
  if(t.size) p.push(fmtSize(t.size));
  return p.join(' · ');
}
async function openAlbum(al, kind) {
  const ov = $('#overlay'); ov.classList.add('show');
  $('#mCover').src = img(al.cover);
  $('#mTitle').textContent = al.title;
  $('#mSub').textContent = `${kind} · ${al.year||''} · loading track list...`;
  $('#mTracks').innerHTML = '<div class="empty">Loading...</div>';
  $('#mDl').onclick = () => { closeModal(); downloadAlbum(al, kind); };
  const artist = (CURRENT_ARTIST && CURRENT_ARTIST.name) || '';
  const qs = `id=${al.id}&artist=${encodeURIComponent(artist)}&title=${encodeURIComponent(albFolder(al))}`;
  const data = await api('/api/album?'+qs);
  if (data.error) { $('#mTracks').innerHTML = `<div class="empty">${esc(data.error)}</div>`; return; }
  const tr = (data.tracks||[]);
  const done = tr.filter(t=>t.downloaded).length;
  const totalSize = tr.reduce((s,t)=>s+(t.size||0), 0);
  $('#mSub').textContent = `${kind} · ${al.year||''}${al.format?' · '+al.format:''} · ${tr.length} tracks · ${done} downloaded`
    + (totalSize?` · ${fmtSize(totalSize)}`:'');
  $('#mTracks').innerHTML = tr.map(t => {
    const specs = trackSpecs(t);
    return `
    <div class="trow">
      <div class="num">${t.number||''}</div>
      <div class="tt"><div class="nm">${esc(t.title)}${t.version?' <span class="ver">('+esc(t.version)+')</span>':''}${t.type==='video'?' 🎬':''}</div><div class="ar">${esc(t.artists)}${t.quality?' · '+esc(t.quality):''}${specs?' · '+specs:''}</div></div>
      <div class="dl ${t.downloaded?'done':''}">${t.downloaded?'✓ downloaded':''}</div>
      <div class="dur">${fmtDur(t.duration)}</div>
    </div>`;
  }).join('') || '<div class="empty">No tracks.</div>';
}
function closeModal(){ $('#overlay').classList.remove('show'); }
document.addEventListener('keydown', e => { if (e.key==='Escape') closeModal(); });

// ---- compare (split view) ----
let compareSel = [];
function inCompare(id){ return compareSel.some(x => String(x.id) === String(id)); }
function toggleCompare(al, kind){
  const i = compareSel.findIndex(x => String(x.id) === String(al.id));
  if (i >= 0) compareSel.splice(i, 1);
  else { if (compareSel.length >= 2) compareSel.shift(); compareSel.push({...al, kind}); }
  refreshCompareUI();
}
function clearCompare(){ compareSel = []; refreshCompareUI(); }
function refreshCompareUI(){
  document.querySelectorAll('.card[data-album-id]').forEach(c =>
    c.classList.toggle('sel', inCompare(c.dataset.albumId)));
  const tray = $('#cmptray');
  tray.classList.toggle('show', compareSel.length > 0);
  $('#cmptrayItems').textContent = compareSel.map(x => x.title).join('  vs  ') || '';
  $('#cmpGo').disabled = compareSel.length < 2;
}
function fetchAlbumTracks(al){
  const artist = (CURRENT_ARTIST && CURRENT_ARTIST.name) || '';
  return api(`/api/album?id=${al.id}&artist=${encodeURIComponent(artist)}&title=${encodeURIComponent(albFolder(al))}`);
}
function trackKey(t){ return (t.title + ' ' + (t.version||'')).trim().toLowerCase(); }
async function openCompare(){
  if (compareSel.length < 2) return;
  const [a, b] = compareSel;
  show('<div class="empty">Loading comparison...</div>');
  const [da, db] = await Promise.all([fetchAlbumTracks(a), fetchAlbumTracks(b)]);
  if (da.error || db.error) return show(`<div class="empty">${esc(da.error||db.error)}</div>`);
  const keysA = new Set((da.tracks||[]).map(trackKey));
  const keysB = new Set((db.tracks||[]).map(trackKey));
  const col = (al, data, otherKeys) => {
    const tr = data.tracks || [];
    const uniq = tr.filter(t => !otherKeys.has(trackKey(t))).length;
    const rows = tr.map(t => {
      const u = !otherKeys.has(trackKey(t));
      return `<div class="trow ${u?'uniq':''}">
        <div class="num">${t.number||''}</div>
        <div class="tt"><div class="nm">${esc(t.title)}${t.version?' <span class="ver">('+esc(t.version)+')</span>':''}</div><div class="ar">${esc(t.artists)}${t.quality?' · '+esc(t.quality):''}</div></div>
        <div class="dl ${t.downloaded?'done':''}">${t.downloaded?'✓':''}</div>
        <div class="dur">${fmtDur(t.duration)}</div>
      </div>`;
    }).join('');
    return `<div class="cmp-col">
      <div class="cmp-colhead">
        <img src="${img(al.cover)}" onerror="this.style.visibility='hidden'">
        <div style="flex:1;min-width:0">
          <div class="h3">${esc(al.title)}</div>
          <div class="muted" style="font-size:12px">${al.kind} · ${al.year||''} · ${tr.length} tracks${al.format?' · '+esc(al.format):''} · id ${al.id}</div>
        </div>
        <button class="btn sm" onclick='downloadAlbum(${attr(al)}, ${attr(al.kind)})'>Download</button>
      </div>
      <div class="cmp-sum">Unique to this edition: <b>${uniq}</b> tracks</div>
      <div class="tracklist cmp-rows">${rows}</div>
    </div>`;
  };
  show(`<div class="cmp-head">
      <button class="btn ghost sm" onclick='CURRENT_ARTIST?openArtist(CURRENT_ARTIST):goSearch()'>← Back</button>
      <div class="section-title" style="margin:0">Compare albums</div>
    </div>
    <div class="muted" style="margin-bottom:14px"><span style="color:#34d399">Green</span> rows = tracks only in one edition.</div>
    <div class="cmp-grid">${col(a, da, keysB)}${col(b, db, keysA)}</div>`);
}

// ---- download ----
// folder name + output template, disambiguated with [id] for duplicate titles
function albFolder(al){ return al.dup ? `${al.title} [${al.id}]` : al.title; }
function albTemplate(al){ return al.dup ? `{album.artist}/${albFolder(al)}/{item.title_version}` : ''; }
function mkItem(al, kind){ return {resource:'album/'+al.id, title:al.title, kind, template:albTemplate(al), artist:(CURRENT_ARTIST&&CURRENT_ARTIST.name)||'', total:al.numberOfTracks||0, cover:al.cover||'', folder:albFolder(al)}; }
function downloadAlbum(al, kind) { startJob([mkItem(al, kind)], `Download: ${al.title}`); }
function downloadAll(which, kind) {
  const list = which === 'albums' ? (window._albums||[]) : (window._singles||[]);
  if (!list.length) return;
  startJob(list.map(al => mkItem(al, kind)), `Download ${list.length} ${kind}`);
}
async function startJob(items, label) {
  const r = await api('/api/download', {method:'POST', headers:{'Content-Type':'application/json'},
    body: JSON.stringify({items, path: $('#path').value, quality: $('#quality').value})});
  if (r.error) return alert(r.error);
  ensureQueuePolling();
}

// ---- queue dock ----
const Q_ICON = {queued:'⏳', downloading:'⬇', cancelling:'…', done:'✓', error:'✗', cancelled:'✕'};
const Q_TEXT = {queued:'Queued', downloading:'Downloading...', cancelling:'Cancelling...', done:'Done', error:'Error', cancelled:'Cancelled'};
let QPOLL = null, lastActive = 0;

function ensureQueuePolling() {
  $('#dock').classList.add('show');
  $('#dockList').classList.remove('collapsed');
  $('#dockToggle').textContent = '▾';
  if (QPOLL) return;
  QPOLL = setInterval(pollQueue, 1000);
  pollQueue();
}
async function pollQueue() {
  const d = await fetch('/api/queue').then(r=>r.json()).catch(()=>({queue:[],active:0}));
  const q = d.queue || [];
  renderQueue(q);
  $('#dockCount').textContent = q.length ? (d.active ? `· ${d.active} in progress` : '· done') : '';
  if (!q.length) { $('#dock').classList.remove('show'); if(QPOLL){clearInterval(QPOLL);QPOLL=null;} }
  else if (d.active === 0 && QPOLL) { clearInterval(QPOLL); QPOLL=null; }
  // when the queue drains, refresh the open artist's download badges
  if (lastActive > 0 && d.active === 0 && CURRENT_ARTIST) setTimeout(()=>openArtist(CURRENT_ARTIST, false), 800);
  lastActive = d.active;
}
function renderQueue(q) {
  window._queue = q;
  $('#dockList').innerHTML = q.map(e => {
    const cancelable = ['queued','downloading','cancelling'].includes(e.status);
    const prog = e.track_total ? `${e.track_done}/${e.track_total} tracks` : '';
    let detail;
    if (e.status === 'downloading') {
      detail = [prog, e.file].filter(Boolean).join(' · ') || 'Downloading...';
    } else if (e.status === 'error') {
      detail = e.file || 'Error';
    } else {
      detail = Q_TEXT[e.status] || e.status;
    }
    const sub = [esc(e.kind), e.artist ? esc(e.artist) : ''].filter(Boolean).join(' · ');
    const hasLog = (e.log && e.log.length);
    const qf = e.status === 'error'
      ? `<div class="qf err"${hasLog?` onclick="showLog('${e.id}')" style="cursor:pointer;text-decoration:underline"`:''}>${esc(detail)}${hasLog?' — view log':''}</div>`
      : `<div class="qf">${esc(detail)}</div>`;
    return `<div class="qrow">
      <span class="qst ${e.status}">${Q_ICON[e.status]||''}</span>
      <div class="qinfo"><div class="qt">${esc(e.title)} <span class="qk">${sub}</span></div>${qf}</div>
      ${cancelable ? `<button class="qcancel" title="Cancel" onclick="cancelOne('${e.id}')">✕</button>` : '<span></span>'}
    </div>`;
  }).join('') || '<div class="empty">Queue is empty.</div>';
}
async function cancelOne(id){ await fetch('/api/cancel',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({id})}); ensureQueuePolling(); }
async function cancelAll(){ await fetch('/api/cancel',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({all:true})}); ensureQueuePolling(); }
async function clearDone(){ await fetch('/api/queue/clear',{method:'POST'}); pollQueue(); }
function showLog(id){ const e=(window._queue||[]).find(x=>x.id===id); if(!e) return; alert('Log — '+e.title+'\n\n'+((e.log||[]).join('\n')||'(no log)')); }
async function openFolder(artist){
  const r = await fetch('/api/open-folder',{method:'POST',headers:{'Content-Type':'application/json'},
    body: JSON.stringify({artist: artist||''})}).then(r=>r.json()).catch(()=>({ok:false}));
  if(!r.ok) alert(r.error || 'Could not open folder');
}
async function downloadAllCovers(){
  const btn=$('#coverAllBtn'); const old=btn.textContent; btn.disabled=true;
  await fetch('/api/covers-all',{method:'POST'}).catch(()=>{});
  const poll = setInterval(async ()=>{
    const j = await fetch('/api/covers-all/status').then(r=>r.json()).catch(()=>null);
    if(!j){ return; }
    if(j.running){
      btn.textContent = `⏳ ${j.done_artists}/${j.total_artists} artists · ${j.saved} covers`;
    } else {
      clearInterval(poll); btn.disabled=false; btn.textContent=old;
      alert(`Cover.jpg for all downloaded albums:\n✓ Saved: ${j.saved}\n• Already present: ${j.exists}\n• No cover: ${j.nocover}\n• Failed: ${j.failed}\n• Artists with unknown id (open once to cache): ${j.no_data}`);
    }
  }, 800);
}
async function downloadCovers(artist){
  const all = [...(window._albums||[]), ...(window._singles||[])];
  const items = all.map(al => ({folder: albFolder(al), cover: al.cover}));
  const btn = $('#coverBtn'); const old = btn.textContent;
  btn.textContent = '⏳ Downloading covers...'; btn.disabled = true;
  const r = await fetch('/api/covers',{method:'POST',headers:{'Content-Type':'application/json'},
    body: JSON.stringify({artist, items})}).then(r=>r.json()).catch(()=>null);
  btn.disabled = false; btn.textContent = old;
  if(!r) return alert('Failed to download covers');
  alert(`Cover.jpg:\n✓ Saved: ${r.saved}\n• Already present: ${r.exists}\n• Not downloaded (skipped): ${r.missing}\n• No cover: ${r.nocover}\n• Failed: ${r.failed}`);
}
function toggleDock(){ const l=$('#dockList'); l.classList.toggle('collapsed'); $('#dockToggle').textContent = l.classList.contains('collapsed')?'▴':'▾'; }

function show(html){ $('#view').innerHTML = html; }
function setBg(url){ const b=$('#pageBg'); if(url){ b.style.backgroundImage=`url('${url}')`; b.classList.add('show'); } else b.classList.remove('show'); }
function esc(s){ return (s==null?'':String(s)).replace(/[&<>"]/g, c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c])); }
// JSON for a single-quoted HTML attribute (escapes ' so titles like "Aaron's Party" don't break onclick)
function attr(o){ return JSON.stringify(o).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/'/g,'&#39;'); }
window.addEventListener('popstate', route);
refreshStatus();
route();
// restore the queue dock if downloads are already running (e.g. after reload)
fetch('/api/queue').then(r=>r.json()).then(d=>{ if (d.queue && d.queue.length) ensureQueuePolling(); }).catch(()=>{});
</script>
</body>
</html>
"""


def main() -> None:
    server = ThreadingHTTPServer((HOST, PORT), Handler)
    url = f"http://{HOST}:{PORT}"
    print(f"tiddl web running at {url}")
    try:
        webbrowser.open(url)
    except Exception:
        pass
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nstopping...")
        server.shutdown()


if __name__ == "__main__":
    main()
