#!/usr/bin/env python3
"""Re-run `lake exe presentation_export` whenever a `.lean` source
file under `formalization/` changes.

Usage (from the formalization/ directory):

    python3 scripts/watch_presentation.py
    python3 scripts/watch_presentation.py --interval 2
    python3 scripts/watch_presentation.py -- --make-pdf=false

Arguments after a literal `--` are forwarded to the exporter.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path


FORMALIZATION_DIR = Path(__file__).resolve().parent.parent
EXCLUDED_DIR_NAMES = {".lake", ".git", "generated", "build"}


@dataclass(frozen=True)
class Snapshot:
    mtimes: dict[Path, int]

    @classmethod
    def take(cls, root: Path) -> "Snapshot":
        result: dict[Path, int] = {}
        for path in root.rglob("*.lean"):
            rel_parts = path.relative_to(root).parts
            if any(p in EXCLUDED_DIR_NAMES for p in rel_parts):
                continue
            try:
                result[path] = path.stat().st_mtime_ns
            except FileNotFoundError:
                pass
        return cls(result)

    def changed_since(self, prev: "Snapshot") -> list[Path]:
        changed = [p for p, m in self.mtimes.items()
                   if prev.mtimes.get(p) != m]
        removed = [p for p in prev.mtimes if p not in self.mtimes]
        return changed + removed


def run_export(extra_args: list[str]) -> int:
    cmd = ["lake", "exe", "presentation_export", *extra_args]
    print(f"\n> {' '.join(cmd)}", flush=True)
    try:
        result = subprocess.run(cmd, cwd=FORMALIZATION_DIR)
    except FileNotFoundError:
        print("error: `lake` not found on PATH", file=sys.stderr)
        return 127
    status = "ok" if result.returncode == 0 else f"failed ({result.returncode})"
    print(f"< presentation_export {status}")
    return result.returncode


def split_forwarded(argv: list[str]) -> tuple[list[str], list[str]]:
    if "--" in argv:
        i = argv.index("--")
        return argv[:i], argv[i + 1:]
    return argv, []


def main() -> None:
    own, forwarded = split_forwarded(sys.argv[1:])
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--interval", type=float, default=1.0,
                        help="Polling interval in seconds (default: 1.0)")
    parser.add_argument("--skip-initial", action="store_true",
                        help="Do not run an initial export on startup")
    args = parser.parse_args(own)

    print(f"Watching {FORMALIZATION_DIR} for *.lean changes "
          f"(interval={args.interval}s). Ctrl-C to quit.")
    state = Snapshot.take(FORMALIZATION_DIR)
    print(f"Tracking {len(state.mtimes)} file(s).")

    if not args.skip_initial:
        run_export(forwarded)

    try:
        while True:
            time.sleep(args.interval)
            curr = Snapshot.take(FORMALIZATION_DIR)
            changed = curr.changed_since(state)
            if not changed:
                continue
            for path in sorted(p.relative_to(FORMALIZATION_DIR)
                               for p in changed):
                print(f"  change: {path}")
            run_export(forwarded)
            state = Snapshot.take(FORMALIZATION_DIR)
    except KeyboardInterrupt:
        print("\nStopping watcher.")


if __name__ == "__main__":
    main()
