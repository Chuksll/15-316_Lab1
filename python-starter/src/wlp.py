"""WLP-based memory safety checker (students implement)."""

from __future__ import annotations

import c0
import solver
import c0_util


def check_safety(
    prog: c0.Program,
) -> bool:
    prog = c0_util.rename_program(prog) # avoid shadowing issues

    var_types = {}

    if prog.args:
        var_types[prog.args[0]] = c0.IntType() # argc
        var_types[prog.args[1]] = c0.ArrayType(c0.IntType()) # argv
    

    def collect_types(stmts: list[c0.Stmt]):
        for s in stmts:
            if isinstance(s, c0.Decl):
                var_types[s.name] = s.type
            elif isinstance(s, c0.AllocArray):
                var_types[s.dest] = c0.ArrayType(s.type)
            elif isinstance(s, c0.ArrRead):
                var_types[s.dest] = c0.IntType()
            elif isinstance(s, c0.Block):
                collect_types(s.stmts)
            elif isinstance(s, c0.If):
                collect_types([s.true_branch])
                if s.false_branch: collect_types([s.false_branch])
            elif isinstance(s, c0.While):
                collect_types([s.body])
    
    collect_types(prog.stmts)
    solver.set_var_types(var_types)

    vcs: list[c0.Exp] = [] # list of verification conditions (VCs) to check

    def exp_safety(e: c0.Exp) -> c0.Exp:
            """Returns a boolean expression that is true if e is safe to evaluate."""
            match e:
                case c0.BinOp(op, l, r):
                    sl, sr = exp_safety(l), exp_safety(r)
                    if op in ("/", "%"):
                        return c0.BinOp("&&", c0.BinOp("&&", sl, sr), c0.BinOp("!=", r, c0.IntConst(0)))
                    return c0.BinOp("&&", sl, sr)
                case c0.UnOp(_, arg) | c0.Length(arg):
                    return exp_safety(arg)
                case c0.ArrayAccess(arr, idx) | c0.ArrSet(arr, idx, _):
                    sa, si = exp_safety(arr), exp_safety(idx)
                    # 0 <= idx < length(arr)
                    bounds = c0.BinOp("&&", c0.BinOp("<=", c0.IntConst(0), idx), 
                                        c0.BinOp("<", idx, c0.Length(arr)))
                    return c0.BinOp("&&", c0.BinOp("&&", sa, si), bounds)
                case _:
                    return c0.BoolConst(True)
                


