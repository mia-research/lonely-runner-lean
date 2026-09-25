"""Find the first feasibility decision where v2 (witness shortcut / warm-started dual simplex) and v1 (cold LP)
disagree, walking v2's search tree with both tests at every call.  Exact."""
import sys
from gmpy2 import mpq
import climb_cells_v1 as v1
import climb_cells_v2 as v2
calls = [0]; mism = []
orig = v2.Search.feasible
def both(self, rows, nparent, wit):
    calls[0] += 1
    w2 = orig(self, rows, nparent, wit)
    c = [v1.Z] * v1.NV; c[v1.TAU] = v1.ONE
    r1 = v1.lp_max(rows, c, [i if c[i] >= 0 else 6 + i for i in range(6)] + [12])
    f1 = r1 is not None and r1[0] > 0
    if f1 != (w2 is not None):
        # which path decided?
        x, basis = wit
        short = x is not None and x[v1.TAU] > 0 and v2.sat(x, rows[nparent:])
        r2 = v2.lp_max(rows, v2.CT, basis)
        mism.append((calls[0], f1, w2 is not None, 'shortcut' if short else 'warm LP', r1 and r1[0], r2 and r2[0], len(rows)))
        print("MISMATCH", mism[-1], flush=True)
        if len(mism) >= 3: raise SystemExit
    return w2
v2.Search.feasible = both
S = v2.Search(9, 1)
roots = S.roots()
for r in roots:
    stack = [r]
    while stack:
        stack.extend(S.children(stack.pop()))
        if calls[0] > 400000: break
print("calls", calls[0], "mismatches", len(mism))
