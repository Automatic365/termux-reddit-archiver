#!/usr/bin/env python3
"""One-command Reddit media archive and deduplicator for Termux."""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import os
import re
import shutil
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from collections import defaultdict
from pathlib import Path
from typing import Iterator

VERSION = "1.10.0"
USER_AGENT = f"termux-reddit-archive/{VERSION} (personal archival use)"
ARCTIC_SEARCH = "https://arctic-shift.photon-reddit.com/api/posts/search"
PULLPUSH_SEARCH = "https://api.pullpush.io/reddit/search/submission/"
UPDATE_URL = "https://raw.githubusercontent.com/Automatic365/termux-reddit-archiver/main/reddit_archive.py"

# Metadata sources in order of preference; later ones are only used when earlier ones fail.
SOURCES = {
    "arctic_shift": {
        "name": "Arctic Shift",
        "url": ARCTIC_SEARCH,
        "params": {"sort": "desc", "limit": "100"},
        "page_delay": 1,
    },
    "pullpush": {
        "name": "PullPush",
        "url": PULLPUSH_SEARCH,
        "params": {"sort": "desc", "sort_type": "created_utc", "size": "100"},
        "page_delay": 4,  # PullPush rate limits at roughly 15 requests per minute
    },
}

# Re-check this far behind the newest known post, to catch posts archived late.
INCREMENTAL_OVERLAP = 3 * 24 * 60 * 60

DEFAULT_MANIFEST_ROOT = Path("/storage/emulated/0/Download/reddit_manifests")
DEFAULT_MEDIA_ROOT = Path("/storage/emulated/0")

IMAGE_EXTENSIONS = {".jpg", ".jpeg", ".png", ".webp", ".gif"}
VIDEO_EXTENSIONS = {".mp4", ".webm", ".mkv", ".mov"}
MEDIA_EXTENSIONS = IMAGE_EXTENSIONS | VIDEO_EXTENSIONS
MIME_EXTENSIONS = {
    "image/jpeg": ".jpg",
    "image/jpg": ".jpg",
    "image/png": ".png",
    "image/gif": ".gif",
    "image/webp": ".webp",
    "video/mp4": ".mp4",
}

# HTTP codes that mean the media is gone for good, not temporarily unavailable.
GONE_HTTP_CODES = {404, 410}

# Give up on an item after this many failed runs (connection problems don't count).
MAX_DOWNLOAD_ATTEMPTS = 5

# Post metadata requests fail fast so a hanging source quickly hands over to the next one.
METADATA_TIMEOUT = 30
METADATA_RETRIES = 3

ARCHIVED_STATUSES = {"downloaded", "existing"}
DUPLICATE_STATUSES = {"deleted_exact_duplicate", "deleted_visual_duplicate"}
DEAD_STATUSES = {"failed_404", "permanently_unavailable"}

# Visual duplicate thresholds: dHash bit difference and aspect ratio tolerance.
VISUAL_HASH_DISTANCE = 4
ASPECT_TOLERANCE = 0.02


def write_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2), encoding="utf-8")
    temporary.replace(path)


def read_json(path: Path, default):
    if not path.is_file():
        return default
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception as error:
        print(f"Could not read {path.name}: {error}", file=sys.stderr)
        return default


def rate_limit_delay(error: urllib.error.HTTPError, default: float = 30) -> float:
    """Seconds to wait after a 429; tolerates missing, decimal or date-valued headers."""
    for header in ("Retry-After", "X-RateLimit-Reset"):
        try:
            return float(error.headers.get(header))
        except (TypeError, ValueError):
            continue
    return default


def request(url: str, retries: int = 5, timeout: float = 60):
    for attempt in range(retries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            return urllib.request.urlopen(req, timeout=timeout)
        except urllib.error.HTTPError as error:
            if error.code == 429 and attempt < retries - 1:
                delay = rate_limit_delay(error)
                print(f"Rate limited; waiting {delay:g} seconds", file=sys.stderr)
                time.sleep(min(max(delay, 1), 300))
                continue
            if error.code == 422 and attempt < retries - 1:
                delay = min(5 * (2**attempt), 60)
                time.sleep(delay)
                continue
            if 500 <= error.code < 600 and attempt < retries - 1:
                time.sleep(2**attempt)
                continue
            raise
        except (urllib.error.URLError, TimeoutError):
            if attempt == retries - 1:
                raise
            time.sleep(2**attempt)
    raise RuntimeError("Request failed")


def request_json(url: str):
    with request(url, retries=METADATA_RETRIES, timeout=METADATA_TIMEOUT) as response:
        return json.load(response)


def normalize_post_response(payload) -> list[dict]:
    if isinstance(payload, list):
        return [item for item in payload if isinstance(item, dict)]
    if isinstance(payload, dict):
        for key in ("data", "posts", "results"):
            value = payload.get(key)
            if isinstance(value, list):
                return [item.get("data", item) for item in value if isinstance(item, dict)]
        children = (payload.get("data") or {}).get("children", []) if isinstance(payload.get("data"), dict) else []
        if children:
            return [item.get("data", item) for item in children if isinstance(item, dict)]
    raise ValueError("Unsupported post response")


def load_saved_posts(destination: Path) -> list[dict]:
    value = read_json(destination, [])
    return [post for post in value if isinstance(post, dict)] if isinstance(value, list) else []


def sort_posts(posts) -> list[dict]:
    return sorted(
        posts,
        key=lambda item: float(item.get("created_utc") or 0),
        reverse=True,
    )


def created(post: dict) -> int | None:
    value = post.get("created_utc")
    return int(float(value)) if value is not None else None


def load_checkpoint(path: Path, saved_posts: list[dict]) -> dict:
    """Per-source crawl state, upgrading the single-source format from v1.7 and earlier."""
    checkpoint = read_json(path, {})
    if not isinstance(checkpoint, dict):
        return {}
    if "complete" in checkpoint or "before" in checkpoint:
        timestamps = [ts for ts in map(created, saved_posts) if ts is not None]
        before = checkpoint.get("before")
        if before is None and not checkpoint.get("complete") and timestamps:
            before = min(timestamps)
        checkpoint = {"arctic_shift": {
            "complete": bool(checkpoint.get("complete")),
            "before": before,
            "newest": max(timestamps) if timestamps else None,
        }}
    return {key: value for key, value in checkpoint.items() if key in SOURCES and isinstance(value, dict)}


def inspect_manifest_history(manifest_dir: Path) -> dict:
    state_file = manifest_dir / "state.json"
    posts_file = manifest_dir / "posts.json"
    checkpoint_file = manifest_dir / "metadata_checkpoint.json"

    saved_posts = load_saved_posts(posts_file)
    state = read_json(state_file, {})
    checkpoint = load_checkpoint(checkpoint_file, saved_posts)

    print(f"--- Manifest Check: {manifest_dir.name} ---")
    if not manifest_dir.exists() or (not state and not saved_posts):
        print("No prior manifest history found. Starting clean session.")
    else:
        downloaded = sum(1 for item in state.values() if item.get("status") in ARCHIVED_STATUSES)
        duplicates = sum(1 for item in state.values() if item.get("status") in DUPLICATE_STATUSES)
        dead = sum(1 for item in state.values() if item.get("status") in DEAD_STATUSES)
        failed = sum(1 for item in state.values() if item.get("status") == "failed")
        print(f"Manifest Directory: {manifest_dir}")
        print(f"Cached Posts:       {len(saved_posts)}")
        print(f"Manifest History:   {len(state)} total items tracked")
        print(f"  - Downloaded:     {downloaded}")
        print(f"  - Duplicates:     {duplicates}")
        print(f"  - Dead/404s:      {dead}")
        print(f"  - Transient fail: {failed}")
        for key, source in SOURCES.items():
            if key in checkpoint:
                status = "Complete" if checkpoint[key].get("complete") else "Partial/In-progress"
            else:
                status = "Not used yet"
            print(f"{source['name'] + ':':<20}{status}")
    print("----------------------------------------\n")
    return state


def merge_post(existing: dict | None, incoming: dict) -> dict:
    """Keep what we already have, filling in any fields the earlier copy was missing."""
    if not existing:
        return incoming
    merged = dict(incoming)
    merged.update({key: value for key, value in existing.items() if value not in (None, "", [], {})})
    return merged


def crawl_source(source: dict, username: str, before: int | None, stop_at: int | None, on_page) -> None:
    """Page backwards from `before` until history ends or posts reach `stop_at`.

    Raises on request errors and malformed pages, so an outage is never
    mistaken for the end of a user's history.
    """
    seen: set[str] = set()
    while True:
        query = {"author": username, **source["params"]}
        if before is not None:
            query["before"] = str(before)
        batch = normalize_post_response(request_json(source["url"] + "?" + urllib.parse.urlencode(query)))
        if not batch:
            return
        timestamps = [ts for ts in map(created, batch) if ts is not None]
        if not timestamps:
            raise ValueError(f"{source['name']} returned posts without timestamps")

        ids = {str(post.get("id") or "") for post in batch} - {""}
        fresh = ids - seen
        seen |= ids
        oldest = min(timestamps)
        # Overlap by one second so posts sharing the boundary timestamp are not
        # skipped, but always move strictly backwards so paging terminates.
        cursor = oldest + 1 if fresh else oldest
        if before is not None:
            cursor = min(cursor, before - 1)
        on_page(batch, cursor, max(timestamps))

        if stop_at is not None and oldest <= stop_at:
            return
        before = cursor
        time.sleep(source["page_delay"])


def fetch_all_posts(username: str, destination: Path) -> tuple[list[dict], str | None]:
    saved_posts = load_saved_posts(destination)
    posts_by_id: dict[str, dict] = {
        str(post["id"]): post for post in saved_posts if post.get("id")
    }
    checkpoint_path = destination.with_name("metadata_checkpoint.json")
    checkpoint = load_checkpoint(checkpoint_path, saved_posts)

    def save_batch(batch: list[dict]) -> None:
        for post in batch:
            post_id = str(post.get("id") or "")
            if post_id:
                posts_by_id[post_id] = merge_post(posts_by_id.get(post_id), post)
        write_json(destination, sort_posts(posts_by_id.values()))

    def sync(key: str) -> None:
        source = SOURCES[key]
        progress = checkpoint.setdefault(key, {})

        if progress.get("newest") is not None:
            # Pick up anything posted since this source's last successful run
            newest = progress["newest"]

            def on_new_page(batch, cursor, page_newest):
                nonlocal newest
                save_batch(batch)
                newest = max(newest, page_newest)

            crawl_source(source, username, None, progress["newest"] - INCREMENTAL_OVERLAP, on_new_page)
            progress["newest"] = newest
            write_json(checkpoint_path, checkpoint)

        if not progress.get("complete"):
            if progress.get("before") is not None:
                print(f"Resuming incomplete {source['name']} metadata fetch from {progress['before']}")

            def on_history_page(batch, cursor, page_newest):
                save_batch(batch)
                progress["before"] = cursor
                progress["newest"] = max(progress.get("newest") or page_newest, page_newest)
                write_json(checkpoint_path, checkpoint)

            crawl_source(source, username, progress.get("before"), None, on_history_page)
            progress["complete"] = True
            write_json(checkpoint_path, checkpoint)

    errors = []
    for key, source in SOURCES.items():
        try:
            sync(key)
        except Exception as error:
            errors.append(f"{source['name']}: {error}")
            fallback = "; trying the next source" if len(errors) < len(SOURCES) else ""
            print(f"{source['name']} unavailable ({error}){fallback}", file=sys.stderr)
            continue
        if errors:
            print(f"Post metadata fetched from {source['name']} instead.")
        else:
            print(f"Post metadata is up to date ({source['name']}).")
        return sort_posts(posts_by_id.values()), None

    return sort_posts(posts_by_id.values()), "; ".join(errors)


def safe_name(value: str, limit: int = 70) -> str:
    value = re.sub(r"[^A-Za-z0-9._ -]+", "_", value).strip(" ._")
    return (value or "untitled")[:limit].rstrip()


def extension_for(metadata: dict, url: str) -> str:
    mime = str(metadata.get("m") or "").lower()
    if mime in MIME_EXTENSIONS:
        return MIME_EXTENSIONS[mime]
    extension = Path(urllib.parse.urlparse(url).path).suffix.lower()
    return extension if extension in MEDIA_EXTENSIONS else ".bin"


def preview_source(post: dict) -> str | None:
    try:
        return html.unescape(post["preview"]["images"][0]["source"]["url"])
    except (KeyError, IndexError, TypeError):
        return None


# Restored v1.3.0 gallery engine
def extract_media(posts: list[dict]) -> tuple[list[dict], list[dict]]:
    items: list[dict] = []
    warnings: list[dict] = []
    seen_urls: set[str] = set()

    for outer in posts:
        outer_id = str(outer.get("id") or "unknown")
        outer_title = str(outer.get("title") or "untitled")
        outer_created = float(outer.get("created_utc") or 0)
        candidates = [outer] + list(outer.get("crosspost_parent_list") or [])

        for post in candidates:
            metadata = post.get("media_metadata") or {}
            gallery = (post.get("gallery_data") or {}).get("items", [])
            order = [entry.get("media_id") for entry in gallery if not entry.get("is_deleted")]
            order = [media_id for media_id in order if media_id] or list(metadata)

            for position, media_id in enumerate(order, 1):
                info = metadata.get(media_id)
                if not info:
                    continue
                source = html.unescape(str((info.get("s") or {}).get("u") or ""))
                extension = extension_for(info, source)
                original = f"https://i.redd.it/{media_id}{extension}"
                if original in seen_urls:
                    continue
                seen_urls.add(original)
                items.append({
                    "post_id": outer_id,
                    "title": outer_title,
                    "created_utc": outer_created,
                    "position": position,
                    "media_id": str(media_id),
                    "url": original,
                    "fallback_urls": [source] if source and source != original else [],
                    "extension": extension,
                    "type": "image",
                })

            direct = html.unescape(str(post.get("url_overridden_by_dest") or post.get("url") or ""))
            parsed = urllib.parse.urlparse(direct)
            host = parsed.netloc.lower().removeprefix("www.")
            direct_extension = Path(parsed.path).suffix.lower()

            if host in {"i.redd.it", "preview.redd.it"} and direct_extension in IMAGE_EXTENSIONS:
                if direct not in seen_urls:
                    seen_urls.add(direct)
                    fallback = preview_source(post)
                    items.append({
                        "post_id": outer_id,
                        "title": outer_title,
                        "created_utc": outer_created,
                        "position": 1,
                        "media_id": Path(parsed.path).stem,
                        "url": direct,
                        "fallback_urls": [fallback] if fallback and fallback != direct else [],
                        "extension": direct_extension,
                        "type": "image",
                    })

            reddit_video = ((post.get("secure_media") or {}).get("reddit_video")
                            or (post.get("media") or {}).get("reddit_video") or {})
            fallback_video = html.unescape(str(reddit_video.get("fallback_url") or ""))
            if fallback_video and fallback_video not in seen_urls:
                seen_urls.add(fallback_video)
                permalink = "https://www.reddit.com" + str(post.get("permalink") or "")
                items.append({
                    "post_id": outer_id,
                    "title": outer_title,
                    "created_utc": outer_created,
                    "position": 1,
                    "media_id": outer_id,
                    "url": fallback_video,
                    "fallback_urls": [],
                    "extension": ".mp4",
                    "type": "video",
                    "page_url": permalink,
                    "hls_url": html.unescape(str(reddit_video.get("hls_url") or "")),
                    "has_audio": reddit_video.get("has_audio"),
                })

            if host == "redgifs.com" and direct not in seen_urls:
                seen_urls.add(direct)
                items.append({
                    "post_id": outer_id,
                    "title": outer_title,
                    "created_utc": outer_created,
                    "position": 1,
                    "media_id": Path(parsed.path).name or outer_id,
                    "url": direct,
                    "fallback_urls": [],
                    "extension": ".mp4",
                    "type": "video",
                    "page_url": direct,
                })

            if post.get("is_gallery") and not metadata:
                warning = {"post_id": str(post.get("id") or outer_id), "reason": "gallery metadata missing"}
                if warning not in warnings:
                    warnings.append(warning)

    return items, warnings


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


class NotMediaError(Exception):
    """The server answered with something other than a media file, such as an HTML error page."""


def download_url(url: str, destination: Path) -> None:
    temporary = destination.with_suffix(destination.suffix + ".part")
    try:
        with request(url) as response, temporary.open("wb") as output:
            content_type = (response.headers.get("Content-Type") or "").lower()
            head = response.read(512)
            # Image and video formats never start with "<" or "{"; pages and JSON errors do
            if (content_type.startswith("text/") or "html" in content_type or "json" in content_type
                    or not head or head.lstrip()[:1] in (b"<", b"{")):
                raise NotMediaError(f"got {content_type or 'an empty response'} instead of media")
            output.write(head)
            shutil.copyfileobj(response, output)
        temporary.replace(destination)
    finally:
        temporary.unlink(missing_ok=True)


def download_reddit_video(item: dict, destination: Path) -> str:
    """Fetch a Reddit-hosted video straight from v.redd.it, avoiding reddit.com
    post pages, which now block logged-out downloaders. Returns the URL used."""
    errors = []
    ffmpeg = shutil.which("ffmpeg")
    if item.get("hls_url") and ffmpeg:
        # The HLS playlist carries both picture and sound; ffmpeg joins them into one mp4
        temporary = destination.with_name(destination.stem + ".part" + destination.suffix)
        try:
            subprocess.run(
                [ffmpeg, "-v", "error", "-y", "-user_agent", USER_AGENT,
                 "-i", item["hls_url"], "-c", "copy", str(temporary)],
                check=True, capture_output=True, timeout=1800,
            )
            if temporary.stat().st_size > 0:
                temporary.replace(destination)
                return item["hls_url"]
            errors.append("ffmpeg produced an empty file")
        except subprocess.CalledProcessError as error:
            errors.append(f"ffmpeg: {error.stderr.decode(errors='replace').strip()[-300:]}")
        except Exception as error:
            errors.append(f"ffmpeg: {error}")
        finally:
            temporary.unlink(missing_ok=True)
    if item.get("has_audio") is False:
        # No sound track, so the plain video file is the whole thing
        download_url(item["url"], destination)
        return item["url"]
    raise RuntimeError("; ".join(errors) or "no direct video source available")


def choose_filename(item: dict) -> str:
    token = safe_name(str(item.get("media_id") or "media"), 30)
    title = safe_name(item["title"], 50)
    return f"{item['post_id']}_{item['position']:02d}_{token}_{title}{item['extension']}"


def video_files(media_folder: Path, stem: str) -> list[Path]:
    """Finished video files for a stem, whatever extension yt-dlp chose.

    Requires the name to be exactly stem + extension, so per-format
    intermediates left by an unfinished merge (stem.f137.mp4) don't count.
    """
    return [
        path for path in media_folder.glob(stem + ".*")
        if path.stem == stem and path.suffix.lower() in VIDEO_EXTENSIONS
        and path.is_file() and path.stat().st_size > 0
    ]


def download_items(items: list[dict], media_folder: Path, state: dict, state_path: Path,
                   count_failures: bool = True) -> tuple[int, int]:
    """Download each item once. `count_failures` is False when this run couldn't
    confirm it was online, so failures don't count towards giving up on an item."""
    yt_dlp = shutil.which("yt-dlp")
    new_downloads = 0
    failures = 0

    for number, item in enumerate(items, 1):
        media_id = str(item.get("media_id") or "")
        key = media_id if media_id else item["url"]

        previous = state.get(key) or state.get(item["url"]) or {}
        status = previous.get("status")

        if status in ARCHIVED_STATUSES:
            print(f"[{number}/{len(items)}] Manifest: previously archived ({media_id or item['url']}) -> skipped")
            continue

        if status in DUPLICATE_STATUSES:
            print(f"[{number}/{len(items)}] Manifest: known duplicate ({media_id or item['url']}) -> skipped")
            continue

        if status in DEAD_STATUSES:
            print(f"[{number}/{len(items)}] Manifest: dead link/unavailable ({media_id or item['url']}) -> skipped")
            continue

        destination = media_folder / choose_filename(item)
        record = {**item, "file": destination.name, "status": "pending"}
        # Whether a failure here says something about the item rather than our connection
        conclusive = count_failures

        try:
            on_disk = video_files(media_folder, destination.stem) if item["type"] == "video" else []
            if on_disk:
                destination = max(on_disk, key=lambda path: path.stat().st_size)
                record["file"] = destination.name
            if destination.is_file() and destination.stat().st_size > 0:
                record["status"] = "existing"
                print(f"[{number}/{len(items)}] existing on disk: {destination.name}")
            elif item["type"] == "video" and item.get("page_url"):
                errors = []
                if item.get("hls_url") or item.get("has_audio") is False:
                    try:
                        record["downloaded_from"] = download_reddit_video(item, destination)
                    except Exception as error:
                        errors.append(f"direct: {error}")
                if "downloaded_from" not in record:
                    # Last resort: let yt-dlp work it out from the post page
                    if not yt_dlp:
                        conclusive = conclusive and bool(errors)
                        raise RuntimeError(" | ".join(errors + ["yt-dlp is required for video downloads"]))
                    stem = destination.with_suffix("")
                    template = str(stem) + ".%(ext)s"
                    try:
                        subprocess.run(
                            [yt_dlp, "--no-playlist", "--no-overwrites", "-o", template, item["page_url"]],
                            check=True,
                        )
                    except subprocess.CalledProcessError as error:
                        raise RuntimeError(" | ".join(errors + [f"yt-dlp exited with status {error.returncode}"]))
                    matches = video_files(media_folder, stem.name)
                    if not matches:
                        raise RuntimeError("yt-dlp completed without producing a file")
                    destination = max(matches, key=lambda path: path.stat().st_size)
                    record["file"] = destination.name
                    record["downloaded_from"] = item["page_url"]
                record["status"] = "downloaded"
                new_downloads += 1
                print(f"[{number}/{len(items)}] downloaded: {record['file']}")
            else:
                errors = []
                http_codes = []
                for candidate in [item["url"]] + list(item.get("fallback_urls") or []):
                    try:
                        download_url(candidate, destination)
                        record["downloaded_from"] = candidate
                        record["status"] = "downloaded"
                        new_downloads += 1
                        break
                    except urllib.error.HTTPError as error:
                        http_codes.append(error.code)
                        errors.append(f"{candidate}: {error}")
                    except NotMediaError as error:
                        http_codes.append("not_media")
                        errors.append(f"{candidate}: {error}")
                    except Exception as error:
                        http_codes.append(None)
                        errors.append(f"{candidate}: {error}")
                if record["status"] != "downloaded":
                    # Only call it dead when every source said the file is gone
                    if http_codes and all(code in GONE_HTTP_CODES for code in http_codes):
                        record["status"] = "failed_404"
                    else:
                        record["status"] = "failed"
                    if all(code is None for code in http_codes):
                        conclusive = False
                    raise RuntimeError(" | ".join(errors))
                print(f"[{number}/{len(items)}] downloaded: {record['file']}")

            if destination.is_file():
                record["bytes"] = destination.stat().st_size
                record["sha256"] = file_sha256(destination)
        except Exception as error:
            if record["status"] == "pending":
                record["status"] = "failed"
            if record["status"] == "failed":
                record["attempts"] = int(previous.get("attempts") or 0) + (1 if conclusive else 0)
                if record["attempts"] >= MAX_DOWNLOAD_ATTEMPTS:
                    record["status"] = "permanently_unavailable"
            record["error"] = str(error)
            failures += 1
            print(f"[{number}/{len(items)}] {record['status']}: {record['file']} ({error})", file=sys.stderr)

        state[key] = record
        write_json(state_path, state)

    return new_downloads, failures


def image_fingerprint(path: Path) -> dict | None:
    """Return width, height and a 64-bit difference hash of the first frame."""
    try:
        probe = subprocess.run(
            ["ffprobe", "-v", "error", "-select_streams", "v:0",
             "-show_entries", "stream=width,height", "-of", "json", str(path)],
            check=True, capture_output=True, timeout=60,
        )
        stream = json.loads(probe.stdout)["streams"][0]
        width, height = int(stream["width"]), int(stream["height"])
        frame = subprocess.run(
            ["ffmpeg", "-v", "error", "-i", str(path), "-frames:v", "1",
             "-vf", "scale=9:8:flags=area,format=gray", "-f", "rawvideo", "-"],
            check=True, capture_output=True, timeout=60,
        ).stdout
    except Exception as error:
        print(f"Could not fingerprint {path.name}: {error}", file=sys.stderr)
        return None
    if len(frame) != 72 or not width or not height:
        return None
    bits = 0
    for row in range(8):
        for column in range(8):
            bits = (bits << 1) | (frame[row * 9 + column] > frame[row * 9 + column + 1])
    return {"width": width, "height": height, "dhash": f"{bits:016x}"}


def similar_hash_pairs(hashes: list[int]) -> Iterator[tuple[int, int]]:
    """Index pairs whose hashes might be within VISUAL_HASH_DISTANCE bits.

    Splits each 64-bit hash into VISUAL_HASH_DISTANCE + 1 bands. Two hashes that
    differ in at most that many bits must agree exactly on at least one band, so
    only images sharing a band need comparing instead of every possible pair.
    Pairs are yielded lazily in (i, j) order, so memory stays linear even when
    many images share a band.
    """
    bands = VISUAL_HASH_DISTANCE + 1
    edges = [round(64 * band / bands) for band in range(bands + 1)]
    keys = [
        [(band, (value >> edges[band]) & ((1 << (edges[band + 1] - edges[band])) - 1)) for band in range(bands)]
        for value in hashes
    ]
    buckets: dict[tuple[int, int], list[int]] = defaultdict(list)
    for index, index_keys in enumerate(keys):
        for key in index_keys:
            buckets[key].append(index)
    for first, index_keys in enumerate(keys):
        later: set[int] = set()
        for key in index_keys:
            later.update(buckets[key])
        for second in sorted(other for other in later if other > first):
            yield first, second


def remove_duplicate(state: dict, key: str, keeper_key: str, media_folder: Path, status: str) -> None:
    record = state[key]
    (media_folder / record["file"]).unlink(missing_ok=True)
    record["status"] = status
    record["duplicate_of"] = state[keeper_key]["file"]
    print(f"Removed {status.removeprefix('deleted_').replace('_', ' ')}: {record['file']} (kept {record['duplicate_of']})")


def deduplicate(media_folder: Path, state: dict, state_path: Path) -> int:
    """Delete exact (same SHA-256) and visual (near-identical image) duplicates."""
    live = {
        key: record for key, record in state.items()
        if record.get("status") in ARCHIVED_STATUSES
        and record.get("file") and (media_folder / record["file"]).is_file()
    }
    for record in live.values():
        if not record.get("sha256"):
            record["sha256"] = file_sha256(media_folder / record["file"])

    def oldest_first(key: str):
        record = state[key]
        return (float(record.get("created_utc") or 0), record["file"])

    removed = 0
    by_hash: dict[str, list[str]] = defaultdict(list)
    for key, record in live.items():
        by_hash[record["sha256"]].append(key)
    for keys in by_hash.values():
        if len(keys) < 2:
            continue
        keeper, *others = sorted(keys, key=oldest_first)
        for key in others:
            remove_duplicate(state, key, keeper, media_folder, "deleted_exact_duplicate")
            del live[key]
            removed += 1

    images = []
    for key, record in live.items():
        if Path(record["file"]).suffix.lower() not in IMAGE_EXTENSIONS:
            continue
        if not record.get("dhash"):
            fingerprint = image_fingerprint(media_folder / record["file"])
            if not fingerprint:
                continue
            record.update(fingerprint)
        # A flat image hashes to all zeros and would match every other flat image
        if int(record["dhash"], 16) == 0:
            continue
        images.append(key)

    def quality(key: str):
        record = state[key]
        return (record["width"] * record["height"], record.get("bytes") or 0, -oldest_first(key)[0])

    deleted: set[str] = set()
    for i, j in similar_hash_pairs([int(state[key]["dhash"], 16) for key in images]):
        first, second = images[i], images[j]
        if first in deleted or second in deleted:
            continue
        a, b = state[first], state[second]
        ratio_a, ratio_b = a["width"] / a["height"], b["width"] / b["height"]
        if abs(ratio_a - ratio_b) > ASPECT_TOLERANCE * max(ratio_a, ratio_b):
            continue
        if bin(int(a["dhash"], 16) ^ int(b["dhash"], 16)).count("1") > VISUAL_HASH_DISTANCE:
            continue
        keeper, loser = (first, second) if quality(first) >= quality(second) else (second, first)
        remove_duplicate(state, loser, keeper, media_folder, "deleted_visual_duplicate")
        deleted.add(loser)
        removed += 1

    write_json(state_path, state)
    return removed


def refresh_gallery(media_folder: Path) -> None:
    if (media_folder / ".nomedia").exists():
        print("Skipping Android gallery scan: .nomedia present in media folder.")
        return
    scanner = shutil.which("termux-media-scan")
    if not scanner:
        return
    try:
        subprocess.run([scanner, "-r", str(media_folder)], check=True, capture_output=True, timeout=120)
        print("Android gallery scan completed.")
    except Exception as error:
        print(f"Gallery scan error: {error}", file=sys.stderr)


def install_path() -> Path | None:
    prefix = os.environ.get("PREFIX")
    if not prefix:
        print("PREFIX is not set. Run inside Termux.", file=sys.stderr)
        return None
    return Path(prefix) / "bin" / "reddit-archive"


def version_tuple(version: str) -> tuple[int, ...]:
    return tuple(int(part) for part in re.findall(r"\d+", version))


def update_self() -> int:
    """Replace the installed command with the latest version from GitHub."""
    destination = install_path()
    if destination is None:
        return 2
    try:
        with request(UPDATE_URL, retries=3, timeout=30) as response:
            source = response.read().decode("utf-8")
    except Exception as error:
        print(f"Could not download the update: {error}", file=sys.stderr)
        return 1

    # Refuse anything that isn't a working copy of this script, so a bad download can't break the install
    match = re.search(r'^VERSION = "([^"]+)"', source, flags=re.MULTILINE)
    try:
        compile(source, UPDATE_URL, "exec")
    except SyntaxError as error:
        match = None
        print(f"Downloaded file is not valid Python ({error}).", file=sys.stderr)
    if not match or "def main(" not in source:
        print("Downloaded file is not reddit-archive; installed version left unchanged.", file=sys.stderr)
        return 1

    latest = match.group(1)
    if destination.is_file():
        installed = re.search(r'^VERSION = "([^"]+)"', destination.read_text(encoding="utf-8", errors="replace"), flags=re.MULTILINE)
        current = installed.group(1) if installed else "unknown"
        if installed and version_tuple(latest) == version_tuple(current):
            print(f"Already up to date ({current}).")
            return 0
        if installed and version_tuple(latest) < version_tuple(current):
            print(f"GitHub has {latest}, older than the installed {current}; not downgrading.")
            return 0
    else:
        current = "not installed"
        if version_tuple(latest) < version_tuple(VERSION):
            print(f"GitHub has {latest}, older than this copy ({VERSION}); run --install to install this copy instead.")
            return 0

    temporary = destination.with_name(".reddit-archive.new")
    try:
        temporary.write_text(source, encoding="utf-8")
        temporary.chmod(0o755)
        temporary.replace(destination)
    finally:
        temporary.unlink(missing_ok=True)
    print(f"Installed reddit-archive {latest}" if current == "not installed" else f"Updated reddit-archive {current} -> {latest}")
    return 0


def install_self() -> int:
    destination = install_path()
    if destination is None:
        return 2
    source = Path(__file__).resolve()
    shutil.copy2(source, destination)
    destination.chmod(0o755)
    print(f"Installed: {destination}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("username", nargs="?", help="Reddit username without u/")
    parser.add_argument("--install", action="store_true", help="Install as the reddit-archive command")
    parser.add_argument("--update", action="store_true", help="Install the latest version from GitHub")
    parser.add_argument("--version", action="version", version=f"%(prog)s {VERSION}")
    parser.add_argument(
        "--manifest-dir",
        type=Path,
        default=DEFAULT_MANIFEST_ROOT,
        help="Parent folder for manifests (default: /storage/emulated/0/Download/reddit_manifests)",
    )
    parser.add_argument(
        "--media-root",
        type=Path,
        default=DEFAULT_MEDIA_ROOT,
        help="Parent directory for media folder (default: /storage/emulated/0)",
    )
    parser.add_argument("--no-dedup", action="store_true", help="Keep duplicate files instead of deleting them")
    args = parser.parse_args()

    if args.install:
        return install_self()
    if args.update:
        return update_self()
    if not args.username:
        parser.error("username is required")
    if not args.no_dedup and (not shutil.which("ffmpeg") or not shutil.which("ffprobe")):
        parser.error("ffmpeg and ffprobe are required for deduplication (or pass --no-dedup)")

    username = re.sub(r"^u/", "", args.username.strip(), flags=re.IGNORECASE)
    if not re.fullmatch(r"[A-Za-z0-9_-]{3,20}", username):
        parser.error("invalid Reddit username")

    user_manifest_dir = args.manifest_dir.expanduser() / username
    user_manifest_dir.mkdir(parents=True, exist_ok=True)
    media_folder = args.media_root.expanduser() / username
    media_folder.mkdir(parents=True, exist_ok=True)

    posts_path = user_manifest_dir / "posts.json"
    state_path = user_manifest_dir / "state.json"

    state = inspect_manifest_history(user_manifest_dir)

    print(f"Media Output:     {media_folder}")
    print(f"Manifest Records: {user_manifest_dir}\n")

    print("Fetching complete public post metadata...")
    posts, metadata_error = fetch_all_posts(username, posts_path)
    if metadata_error:
        print(f"Metadata fetch stopped early ({metadata_error}); it will resume next run.", file=sys.stderr)

    items, warnings = extract_media(posts)
    print(f"Found {len(posts)} total posts and {len(items)} media candidates")
    if not shutil.which("yt-dlp") and any(item["type"] == "video" for item in items):
        print("yt-dlp not found: videos will be skipped and retried next run (pip install yt-dlp)", file=sys.stderr)

    new_downloads, failures = download_items(items, media_folder, state, state_path, count_failures=not metadata_error)
    write_json(state_path, state)

    if new_downloads > 0:
        print(f"\n{new_downloads} new file(s) downloaded.")
    elif not failures:
        print("\nAll media items already accounted for in manifest. Nothing downloaded.")
    if failures:
        print(f"\n{failures} item(s) failed this run; see the errors above. Each is retried on later runs, up to {MAX_DOWNLOAD_ATTEMPTS} tries.")

    duplicates_removed = 0
    if not args.no_dedup:
        print("\nChecking for duplicates...")
        duplicates_removed = deduplicate(media_folder, state, state_path)

    refresh_gallery(media_folder)

    remaining = [p.name for p in media_folder.iterdir() if p.is_file() and p.suffix.lower() in MEDIA_EXTENSIONS]
    print("\nRun Complete")
    print(f"Clean Media Files:  {len(remaining)}")
    print(f"New Downloads:      {new_downloads}")
    print(f"Failed:             {failures}")
    print(f"Duplicates Removed: {duplicates_removed}")
    return 4 if metadata_error else 0


if __name__ == "__main__":
    raise SystemExit(main())
