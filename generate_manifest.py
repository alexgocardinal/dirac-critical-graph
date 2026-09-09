#!/usr/bin/env python3
"""Regenerate MANIFEST.sha256 deterministically from repository files."""

from hashlib import sha256
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OUTPUT = ROOT / "MANIFEST.sha256"
SKIP_DIRS = {".git", ".lake", "build", "__pycache__"}
SKIP_SUFFIXES = {".olean", ".ilean", ".o", ".out", ".pyc"}


def included(path: Path) -> bool:
    relative = path.relative_to(ROOT)
    return (
        path.is_file()
        and path != OUTPUT
        and not any(part in SKIP_DIRS for part in relative.parts)
        and path.suffix not in SKIP_SUFFIXES
        and path.name != ".DS_Store"
    )


files = sorted(
    (path for path in ROOT.rglob("*") if included(path)),
    key=lambda path: path.relative_to(ROOT).as_posix(),
)

lines = []
for path in files:
    digest = sha256(path.read_bytes()).hexdigest()
    lines.append(f"{digest}  {path.relative_to(ROOT).as_posix()}")

OUTPUT.write_text("\n".join(lines) + "\n", encoding="utf-8")
print(f"Wrote {OUTPUT.name} with {len(lines)} entries")
