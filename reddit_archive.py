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
from itertools import combinations
from pathlib import Path

VERSION = "1.7.0"
USER_AGENT = f"termux-reddit-archive/{VERSION} (personal archival use)"
ARCTIC_SEARCH = "https://arctic-shift.photon-reddit.com/api/posts/search"

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


def request(url: str, retries: int = 5):
    for attempt in range(retries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            return urllib.request.urlopen(req, timeout=60)
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
    with request(url) as response:
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


def inspect_manifest_history(manifest_dir: Path) -> dict:
    state_file = manifest_dir / "state.json"
    posts_file = manifest_dir / "posts.json"
    checkpoint_file = manifest_dir / "metadata_checkpoint.json"

    saved_posts = load_saved_posts(posts_file)
    state = read_json(state_file, {})
    checkpoint = read_json(checkpoint_file, {})

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
        print(f"Metadata Status:    {'Complete' if checkpoint.get('complete') else 'Partial/In-progress'}")
    print("----------------------------------------\n")
    return state


def fetch_all_posts(username: str, destination: Path) -> tuple[list[dict], str | None]:
    saved_posts = load_saved_posts(destination)
    posts_by_id: dict[str, dict] = {
        str(post["id"]): post for post in saved_posts if post.get("id")
    }
    checkpoint_path = destination.with_name("metadata_checkpoint.json")
    checkpoint = read_json(checkpoint_path, {})
    if not isinstance(checkpoint, dict):
        checkpoint = {}

    def crawl(before: int | None, stop_when_caught_up: bool, track_checkpoint: bool) -> None:
        """Page backwards from `before`. Raises on request errors."""
        while True:
            query = {"author": username, "sort": "desc", "limit": "100"}
            if before is not None:
                query["before"] = str(before)
            batch = normalize_post_response(request_json(ARCTIC_SEARCH + "?" + urllib.parse.urlencode(query)))

            if not batch:
                if track_checkpoint:
                    write_json(checkpoint_path, {"complete": True, "before": before, "posts_saved": len(posts_by_id)})
                return

            new_posts_found = 0
            for post in batch:
                post_id = str(post.get("id") or "")
                if not post_id:
                    continue
                if post_id not in posts_by_id:
                    new_posts_found += 1
                posts_by_id[post_id] = post
            write_json(destination, sort_posts(posts_by_id.values()))

            timestamps = [int(float(item["created_utc"])) for item in batch if item.get("created_utc") is not None]
            if not timestamps:
                return
            oldest = min(timestamps)
            if before is not None and oldest >= before:
                return
            before = oldest

            if track_checkpoint:
                write_json(checkpoint_path, {"complete": False, "before": before, "posts_saved": len(posts_by_id)})

            # Reached posts we already have: everything newer has been collected
            if stop_when_caught_up and new_posts_found == 0:
                return
            time.sleep(1)

    try:
        if posts_by_id:
            # Pick up anything posted since the last run
            crawl(None, stop_when_caught_up=True, track_checkpoint=False)
            if checkpoint.get("complete"):
                print("Upstream post archive is up to date.")
                return sort_posts(posts_by_id.values()), None

            # A previous metadata fetch stopped early; resume where it left off
            resume = checkpoint.get("before")
            if resume is None:
                timestamps = [int(float(post["created_utc"])) for post in saved_posts if post.get("created_utc") is not None]
                resume = min(timestamps) if timestamps else None
            print(f"Resuming incomplete metadata fetch from {resume}")
            crawl(resume, stop_when_caught_up=False, track_checkpoint=True)
        else:
            crawl(None, stop_when_caught_up=False, track_checkpoint=True)
    except Exception as error:
        return sort_posts(posts_by_id.values()), str(error)

    return sort_posts(posts_by_id.values()), None


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


def download_url(url: str, destination: Path) -> None:
    temporary = destination.with_suffix(destination.suffix + ".part")
    try:
        with request(url) as response, temporary.open("wb") as output:
            shutil.copyfileobj(response, output)
        temporary.replace(destination)
    finally:
        temporary.unlink(missing_ok=True)


def choose_filename(item: dict) -> str:
    token = safe_name(str(item.get("media_id") or "media"), 30)
    title = safe_name(item["title"], 50)
    return f"{item['post_id']}_{item['position']:02d}_{token}_{title}{item['extension']}"


def video_files(media_folder: Path, stem: str) -> list[Path]:
    """Finished video files for a stem, whatever extension yt-dlp chose."""
    return [
        path for path in media_folder.glob(stem + ".*")
        if path.suffix.lower() in VIDEO_EXTENSIONS and path.is_file() and path.stat().st_size > 0
    ]


def download_items(items: list[dict], media_folder: Path, state: dict, state_path: Path) -> int:
    yt_dlp = shutil.which("yt-dlp")
    new_downloads = 0

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
            print(f"[{number}/{len(items)}] Manifest: dead link/404 ({media_id or item['url']}) -> skipped")
            continue

        destination = media_folder / choose_filename(item)
        record = {**item, "file": destination.name, "status": "pending"}

        try:
            on_disk = video_files(media_folder, destination.stem) if item["type"] == "video" else []
            if on_disk:
                destination = max(on_disk, key=lambda path: path.stat().st_size)
                record["file"] = destination.name
            if destination.is_file() and destination.stat().st_size > 0:
                record["status"] = "existing"
                print(f"[{number}/{len(items)}] existing on disk: {destination.name}")
            elif item["type"] == "video" and item.get("page_url"):
                if not yt_dlp:
                    raise RuntimeError("yt-dlp is required for video downloads")
                stem = destination.with_suffix("")
                template = str(stem) + ".%(ext)s"
                subprocess.run(
                    [yt_dlp, "--no-playlist", "--no-overwrites", "-o", template, item["page_url"]],
                    check=True,
                )
                matches = video_files(media_folder, stem.name)
                if not matches:
                    raise RuntimeError("yt-dlp completed without producing a file")
                destination = max(matches, key=lambda path: path.stat().st_size)
                record["file"] = destination.name
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
                    except Exception as error:
                        http_codes.append(None)
                        errors.append(f"{candidate}: {error}")
                if record["status"] != "downloaded":
                    # Only call it dead when every source said the file is gone
                    if http_codes and all(code in GONE_HTTP_CODES for code in http_codes):
                        record["status"] = "failed_404"
                    else:
                        record["status"] = "failed"
                    raise RuntimeError(" | ".join(errors))
                print(f"[{number}/{len(items)}] downloaded: {record['file']}")

            if destination.is_file():
                record["bytes"] = destination.stat().st_size
                record["sha256"] = file_sha256(destination)
        except Exception as error:
            if record["status"] == "pending":
                record["status"] = "failed"
            record["error"] = str(error)
            print(f"[{number}/{len(items)}] {record['status']}: {record['file']} ({error})", file=sys.stderr)

        state[key] = record
        write_json(state_path, state)

    return new_downloads


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


def similar_hash_pairs(hashes: list[int]) -> list[tuple[int, int]]:
    """Index pairs whose hashes might be within VISUAL_HASH_DISTANCE bits.

    Splits each 64-bit hash into VISUAL_HASH_DISTANCE + 1 bands. Two hashes that
    differ in at most that many bits must agree exactly on at least one band, so
    only images sharing a band need comparing instead of every possible pair.
    """
    bands = VISUAL_HASH_DISTANCE + 1
    edges = [round(64 * band / bands) for band in range(bands + 1)]
    buckets: dict[tuple[int, int], list[int]] = defaultdict(list)
    for index, value in enumerate(hashes):
        for band in range(bands):
            low, high = edges[band], edges[band + 1]
            buckets[(band, (value >> low) & ((1 << (high - low)) - 1))].append(index)
    pairs: set[tuple[int, int]] = set()
    for members in buckets.values():
        pairs.update(combinations(members, 2))
    return sorted(pairs)


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


def install_self() -> int:
    prefix = os.environ.get("PREFIX")
    if not prefix:
        print("PREFIX is not set. Run inside Termux.", file=sys.stderr)
        return 2
    destination = Path(prefix) / "bin" / "reddit-archive"
    source = Path(__file__).resolve()
    shutil.copy2(source, destination)
    destination.chmod(0o755)
    print(f"Installed: {destination}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("username", nargs="?", help="Reddit username without u/")
    parser.add_argument("--install", action="store_true", help="Install as the reddit-archive command")
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

    new_downloads = download_items(items, media_folder, state, state_path)
    write_json(state_path, state)

    if new_downloads > 0:
        print(f"\n{new_downloads} new file(s) downloaded.")
    else:
        print("\nAll media items already accounted for in manifest. Nothing downloaded.")

    duplicates_removed = 0
    if not args.no_dedup:
        print("\nChecking for duplicates...")
        duplicates_removed = deduplicate(media_folder, state, state_path)

    refresh_gallery(media_folder)

    remaining = [p.name for p in media_folder.iterdir() if p.is_file() and p.suffix.lower() in MEDIA_EXTENSIONS]
    print("\nRun Complete")
    print(f"Clean Media Files:  {len(remaining)}")
    print(f"New Downloads:      {new_downloads}")
    print(f"Duplicates Removed: {duplicates_removed}")
    return 4 if metadata_error else 0


if __name__ == "__main__":
    raise SystemExit(main())
