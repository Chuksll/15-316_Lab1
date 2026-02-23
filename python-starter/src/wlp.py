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

    Pre = c0.BoolConst(True)
    if prog.requires:
        for req in prog.requires: Pre = c0.BinOp("&&", Pre, req)

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
                
    def wlp_stmt(s: c0.Stmt, Q: c0.Exp) -> c0.Exp:
        """Computes wlp(s, Q)."""
        match s:
            case c0.Decl(t, name, init):
                if init is None: # C0 defaults
                    init = c0.ArrMake(c0.IntConst(0)) if isinstance(t, c0.ArrayType) else c0.IntConst(0)
                return c0.BinOp("&&", exp_safety(init), c0_util.subst_exp(Q, name, init))
            
            case c0.Assign(dest, src):
                return c0.BinOp("&&", exp_safety(src), c0_util.subst_exp(Q, dest, src))
            
            case c0.AllocArray(dest, _, count):
                safe_alloc = c0.BinOp("&&", exp_safety(count), c0.BinOp("<=", c0.IntConst(0), count))
                return c0.BinOp("&&", safe_alloc, c0_util.subst_exp(Q, dest, c0.ArrMake(count)))
            
            case c0.ArrRead(dest, arr, idx):
                return c0.BinOp("&&", exp_safety(c0.ArrayAccess(arr, idx)), 
                               c0_util.subst_exp(Q, dest, c0.ArrayAccess(arr, idx)))
            
            case c0.ArrWrite(arr, idx, val):
                # Update: arr = ArrSet(arr, idx, val)
                safety = exp_safety(c0.ArrSet(arr, idx, val))
                if isinstance(arr, c0.Var):
                    return c0.BinOp("&&", safety, c0_util.subst_exp(Q, arr.name, c0.ArrSet(arr, idx, val)))
                return c0.BinOp("&&", safety, Q)
            
            case c0.Block(stmts):
                for stmt in reversed(stmts): Q = wlp_stmt(stmt, Q)
                return Q
            
            case c0.If(cond, t, f):
                wt, wf = wlp_stmt(t, Q), (wlp_stmt(f, Q) if f else Q)
                return c0.BinOp("&&", exp_safety(cond), 
                        c0.BinOp("&&", c0.BinOp("=>", cond, wt), c0.BinOp("=>", c0.UnOp("!", cond), wf)))
            
            case c0.While(cond, invs, body):
                I = c0.BoolConst(True)
                for inv in invs: I = c0.BinOp("&&", I, inv)
                
                # Separate out loop VCs
                preservation = c0.BinOp("=>", c0.BinOp("&&", I, cond), wlp_stmt(body, I))
                vcs.append(c0.BinOp("=>", Pre, preservation)) # Preservation

                exit_condition = c0.BinOp("=>", c0.BinOp("&&", I, c0.UnOp("!", cond)), Q)
                vcs.append(c0.BinOp("=>", Pre, exit_condition))   # Exit
                
                # Ensure loop components are safe to evaluate
                safe_loop = exp_safety(cond)
                for inv in invs: safe_loop = c0.BinOp("&&", safe_loop, exp_safety(inv))
                return c0.BinOp("&&", safe_loop, I)
            
            case c0.Assert(cond):
                return c0.BinOp("&&", exp_safety(cond), c0.BinOp("&&", cond, Q))
            
            case c0.Return(val):
                return c0.BinOp("&&", exp_safety(val), c0_util.subst_result(Q, val)) if val else Q
            
            case c0.Error(_):
                return c0.BoolConst(True)
            case _: return Q

    # 3. Final Verification Condition Generation
    Q_final = c0.BoolConst(True)
    if prog.ensures:
        for ens in prog.ensures: Q_final = c0.BinOp("&&", Q_final, ens)

    
    vcs.append(c0.BinOp("=>", Pre, wlp_stmt(c0.Block(prog.stmts), Q_final)))
    
    # 4. Discharge VCs to Z3
    for vc in vcs:
        if not solver.check_validity(c0_util.simplify(vc)):
            return False
            
    return True


