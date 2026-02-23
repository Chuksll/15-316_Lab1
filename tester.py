#!/usr/bin/env python3
import argparse
import glob
import subprocess
import sys
from pathlib import Path

def run_one(script: Path, testfile: str) -> int:
    tf = str(Path(testfile).resolve())
    print(f"==> {testfile}")
    p = subprocess.run([str(script), tf], cwd=str(script.parent))
    return p.returncode

def main() -> int:
    ap = argparse.ArgumentParser(
        description="Run c0_vc.sh over multiple .c0 test files (like a shell loop)."
    )
    ap.add_argument(
        "paths",
        nargs="+",
        help="Files/dirs/globs of .c0 tests (e.g., tests/*.c0 mytests/ foo.c0).",
    )
    ap.add_argument(
        "--script",
        default="python-starter/c0_vc.sh",
        help="Path to c0_vc.sh (default: python-starter/c0_vc.sh).",
    )
    ap.add_argument(
        "--fail-fast",
        action="store_true",
        help="Stop at the first failing test (nonzero exit).",
    )
    args = ap.parse_args()

    script = Path(args.script).resolve()
    if not script.exists():
        print(f"error: script not found: {script}", file=sys.stderr)
        return 2

    files: list[str] = []
    for p in args.paths:
        expanded = glob.glob(p)
        if expanded:
            for e in expanded:
                pe = Path(e)
                if pe.is_dir():
                    files.extend(sorted(str(x) for x in pe.rglob("*.c0")))
                else:
                    files.append(str(pe))
            continue

        pp = Path(p)
        if pp.is_dir():
            files.extend(sorted(str(x) for x in pp.rglob("*.c0")))
        elif pp.exists():
            files.append(str(pp))

    seen = set()
    files = [f for f in files if not (f in seen or seen.add(f))]

    if not files:
        print("error: no .c0 files found", file=sys.stderr)
        return 2


    worst_rc = 0
    unsafe = [f for f in files if "unsafe" in f]
    safe = [f for f in files if "unsafe" not in f]
    for f in unsafe + safe:
        rc = run_one(script, f)
        if rc != 0:
            worst_rc = rc
            if args.fail_fast:
                return rc
            
    return worst_rc

if __name__ == "__main__":
    raise SystemExit(main())



