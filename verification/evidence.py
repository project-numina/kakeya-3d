"""Source identities and receipts shared by the verification commands."""

import hashlib
import json
import os
from pathlib import Path
import subprocess


def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def capture(root, *args):
    return subprocess.check_output(args, cwd=root, text=True).strip()


def inventory(root):
    root = Path(root).resolve()
    names = subprocess.check_output(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
        cwd=root).decode().split("\0")
    result = {}
    for name in sorted(set(filter(None, names))):
        path = root / name
        if path.is_symlink() or not path.resolve().is_relative_to(root):
            raise RuntimeError(f"Source path is a symlink or escapes the checkout: {name}")
        result[name] = digest(path)
    if not result:
        raise RuntimeError(f"No source files found in {root}")
    return result


def identity(root):
    files = inventory(root)
    return {
        "commit": capture(root, "git", "rev-parse", "HEAD"),
        "status": capture(root, "git", "status", "--porcelain"),
        "files": len(files),
        "source_sha256": hashlib.sha256(
            json.dumps(files, sort_keys=True).encode()).hexdigest(),
    }


def save_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")
    os.replace(temporary, path)
