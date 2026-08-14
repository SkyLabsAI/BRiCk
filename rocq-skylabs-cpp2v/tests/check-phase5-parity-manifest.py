#!/usr/bin/env python3
"""Reject silent growth or shrinkage of the Phase 5 fixture parity set."""

from pathlib import Path
import os
import sys

if source_root := os.environ.get("DUNE_SOURCEROOT"):
    TESTS = (
        Path(source_root)
        / "fmdeps/BRiCk/rocq-skylabs-cpp2v/tests"
    )
else:
    TESTS = Path(__file__).resolve().parent
MANIFEST = TESTS / "phase5-parity-manifest.tsv"
CATEGORIES = {
    "production-helper",
    "production-makefile",
    "production-manual",
    "focused-builder",
    "source-info",
    "name-test",
    "expected-failure",
}
PRODUCTION = {
    "production-helper",
    "production-makefile",
    "production-manual",
}


def fail(message: str) -> None:
    print(f"phase5 fixture manifest error: {message}", file=sys.stderr)
    raise SystemExit(1)


entries: dict[str, str] = {}
for number, raw in enumerate(MANIFEST.read_text().splitlines(), 1):
    if not raw or raw.startswith("#"):
        continue
    fields = raw.split("\t")
    if len(fields) != 2:
        fail(f"line {number} is not CATEGORY<TAB>PATH")
    category, relative = fields
    if category not in CATEGORIES:
        fail(f"line {number} has unknown category {category!r}")
    if relative in entries:
        fail(f"duplicate input {relative!r}")
    entries[relative] = category

actual = {
    path.relative_to(TESTS).as_posix()
    for suffix in ("*.cpp", "*.hpp")
    for path in TESTS.rglob(suffix)
}
listed = set(entries)
if missing := sorted(actual - listed):
    fail("unclassified inputs: " + ", ".join(missing))
if stale := sorted(listed - actual):
    fail("stale inputs: " + ", ".join(stale))

for relative, category in entries.items():
    directory = (TESTS / relative).parent
    if category == "production-helper":
        run = directory / "run.t"
        if not run.exists() or "check_cpp2v" not in run.read_text():
            fail(f"{relative!r} no longer uses a check_cpp2v helper")
    elif category == "production-makefile":
        current = directory
        while current != TESTS and not (current / "Makefile").exists():
            current = current.parent
        if current == TESTS and not (current / "Makefile").exists():
            fail(f"{relative!r} has no enclosing Makefile")

production_count = sum(category in PRODUCTION for category in entries.values())
print(
    f"phase5 fixture manifest: {len(entries)} inputs "
    f"({production_count} production, {len(entries) - production_count} "
    "focused/excluded)"
)
