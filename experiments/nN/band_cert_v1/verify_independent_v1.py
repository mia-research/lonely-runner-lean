"""Independent re-check of cert15.pkl (main session, 2026-09-27).  Shares no code with verify.py.
Formulation: along every chain of cells, the robust clear set S of R (clear for every speed of every box above, and for
the slowest runner) is recomputed from scratch; at each s2-leaf [a2,b2], every x in [1, b2] must have a clear instant
in S: for a component [p,q] of S, x does iff x in [(8k+1)/q, (8k+7)/p] for some k >= 0 (x*[p,q] meets [8k+1, 8k+7]).
So the leaf passes iff the union of those closed intervals covers [1, b2].  Exact Fractions throughout."""
import sys, pickle
from fractions import Fraction as F
from math import floor
from multiprocessing import Pool

def robust(a, b, lo, hi):
    """closed R-intervals in [lo,hi] clear for every speed x in [a,b]: R in [(8k+1)/a, (8k+7)/b]."""
    out = []; k = 0
    if a * lo > 8: k = int((a * lo - 8) // 8)
    while True:
        L = F(8 * k + 1) / a; H = F(8 * k + 7) / b
        if L > hi: return out
        L, H = max(L, lo), min(H, hi)
        if L <= H: out.append((L, H))
        k += 1

def meet(A, B):
    out = []
    for (a1, b1) in A:
        for (a2, b2) in B:
            if a2 > b1: break
            lo, hi = max(a1, a2), min(b1, b2)
            if lo <= hi: out.append((lo, hi))
    return sorted(out)

def covers(S, top):
    ivs = []
    for (p, q) in S:
        k = 0
        while True:
            lo = F(8 * k + 1) / q
            if lo > top: break
            ivs.append((lo, F(8 * k + 7) / p)); k += 1
    ivs.sort(); reach = F(1)
    for lo, hi in ivs:
        if lo > reach: return False
        if hi > reach: reach = hi
        if reach >= top: return True
    return reach >= top

def walk(node, S, level, lo, hi, counts):
    assert node and F(node[0][0]) == lo and F(node[-1][1]) == hi, ("tiling ends", level)
    prev = lo
    for (a, b, sub) in node:
        a, b = F(a), F(b)
        assert a == prev and a < b, ("tiling gap", level)
        prev = b
        S2 = meet(S, robust(a, b, S[0][0], S[-1][1])) if S else []
        assert S2, ("empty clear set", level, a, b)
        counts[0] += 1
        if level == 2:
            assert sub is None
            assert covers(S2, b), ("leaf not covered", a, b)
            counts[1] += 1
        else:
            walk(sub, S2, level - 1, F(1), b, counts)

def job(args):
    a, b, tree, Rhi = args; counts = [0, 0]
    try:
        walk(tree, [(F(1), F(7)), (F(9), F(Rhi))], 6, F(a), F(b), counts)
        return True, counts, None
    except AssertionError as e:
        return False, counts, repr(e.args)[:300]

if __name__ == '__main__':
    cert = pickle.load(open(sys.argv[1], 'rb')); top = cert['top']; Rhi = F(cert['Rhi'])
    assert F(top[0][0]) == 7 and F(top[-1][1]) == 9
    assert all(F(top[i][1]) == F(top[i + 1][0]) for i in range(len(top) - 1))
    with Pool(10) as p: res = p.map(job, [(a, b, t, Rhi) for a, b, t in top], chunksize=1)
    print("Rhi =", Rhi, " cells:", sum(r[1][0] for r in res), " leaves:", sum(r[1][1] for r in res))
    for ok, c, msg in res:
        if not ok: print("FAIL", msg)
    print("INDEPENDENT CHECK PASSED" if all(r[0] for r in res) else "INDEPENDENT CHECK FAILED")
