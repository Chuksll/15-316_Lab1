import os
import sys

# Prefer vendored dependencies (so the starter works out-of-the-box after `make`).
sys.path.append(os.path.join(os.path.dirname(__file__), "..", "vendor"))

from parse import file_parse
from wlp import check_safety


def print_and_exit(msg: str, code: int) -> None:
    try:
        print(msg)
    except BrokenPipeError:
        pass
    raise SystemExit(code)


class CmdLineArgs:
    def __init__(
        self,
        filename: str,
        *,
        verbose: bool,
        print_vc: bool,
        small_cex: bool,
        small_cex_max: int,
    ):
        self.filename = filename
        self.verbose = verbose
        self.print_vc = print_vc
        self.small_cex = small_cex
        self.small_cex_max = small_cex_max


def parse_cmd_line_args(argv: list[str]) -> CmdLineArgs:
    verbose = False
    print_vc = False
    small_cex = False
    small_cex_max = 32
    positional: list[str] = []

    i = 0
    while i < len(argv):
        a = argv[i]
        if a in ("--verbose", "-v"):
            verbose = True
            i += 1
        elif a == "--print-vc":
            print_vc = True
            i += 1
        elif a == "--small-cex":
            small_cex = True
            i += 1
        elif a == "--small-cex-max":
            if i + 1 >= len(argv):
                print_and_exit("expected integer after --small-cex-max", 1)
            small_cex = True
            try:
                small_cex_max = int(argv[i + 1])
            except Exception:
                print_and_exit("expected integer after --small-cex-max", 1)
            i += 2
        elif a.startswith("-"):
            print_and_exit("error", 1)
        else:
            positional.append(a)
            i += 1

    if len(positional) != 1:
        print_and_exit("error", 1)

    return CmdLineArgs(
        positional[0],
        verbose=verbose,
        print_vc=print_vc,
        small_cex=small_cex,
        small_cex_max=small_cex_max,
    )


def main() -> None:
    cmd = parse_cmd_line_args(sys.argv[1:])
    try:
        with open(cmd.filename, "r", encoding="utf-8") as f:
            src = f.read()
    except Exception:
        print_and_exit("error", 1)

    try:
        prog = file_parse(src)
    except Exception as e:
        if cmd.verbose:
            print(e, file=sys.stderr)
        print_and_exit("error", 1)

    try:
        ok = check_safety(
            prog,
            verbose=cmd.verbose,
            print_vc=cmd.print_vc,
            small_cex=cmd.small_cex,
            small_cex_max=cmd.small_cex_max,
        )
    except NotImplementedError:
        print_and_exit("error", 1)
    except Exception as e:
        if cmd.verbose:
            print(e, file=sys.stderr)
        print_and_exit("error", 1)

    if ok:
        print_and_exit("valid", 0)
    else:
        print_and_exit("unsafe", 2)


if __name__ == "__main__":
    main()
