"""WLP-based memory safety checker (students implement)."""

from __future__ import annotations

import c0
import solver


def check_safety(
    prog: c0.Program,
    *,
    verbose: bool = False,
    print_vc: bool = False,
    small_cex: bool = False,
    small_cex_max: int = 32,
) -> bool:
    raise NotImplementedError("check_safety is not implemented")
