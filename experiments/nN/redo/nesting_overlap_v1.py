"""E389 (2026-10-05), nesting_overlap_v1: can ANY reading 7 nest every window of the first six at once?

Owner: "keep going on layer 5" (after E388).  For a crosser with first six readings x[:6] (the tree members' own six), the windows of
K6 in [1,7] and K'_6 in [9,15] (exact).  Reading 7 at speed v blocks a window [a,b] entirely iff the window lies in one of its zones:
exists lap j >= 1 with (8j-1)/v < a and b < (8j+1)/v, i.e. v in ((8j-1)/a, (8j+1)/b).  K7 empty in a window = every window of that
window's K6 nested.  Question run: the set of v in (rho6, 7 rho6] (R8: not fast) that nests ALL windows of BOTH [1,7] and [9,15]
(= the crossing of both windows, landing >= 17) is computed exactly as an intersection of finite unions of open intervals.
Also the set for [1,7] alone (the crossing, E-gate) and the member's own rho7 (must lie in it).  Every member whose both-windows set
is non-empty is listed individually.  Exact (Fractions).
"""
import sys, pickle
from fractions import Fraction as F
from multiprocessing import Pool
sys.path.insert(0, '../band_cert_v1')
from core import clear_set

def nest_set(wins, lo, hi):
    """open intervals of v in (lo, hi] nesting every window in wins."""
    cur = [(lo, hi)]
    for a, b in wins:
        ints = []
        j = 1
        while True:
            L = F(8 * j - 1) / a if a > 0 else None
            if L is not None and L >= hi:
                break
            U = F(8 * j + 1) / b if b > 0 else None
            if U is not None and L < U:
                ints.append((L, U))
            j += 1
            if j > 2000:
                break
        new = []
        for (c, d) in cur:
            for (e, f) in ints:
                l, u = max(c, e), min(d, f)
                if l < u:
                    new.append((l, u))
        cur = new
        if not cur:
            return cur
    return cur

def work(items):
    out = []
    for idx, x in items:
        if clear_set(x, F(1), F(7)):
            continue
        six = x[:6]
        k6A = clear_set(six, F(1), F(7)); k6B = clear_set(six, F(9), F(15))
        lo, hi = x[5], 7 * x[5]
        sA = nest_set(k6A, lo, hi)
        sAB = nest_set(k6A + k6B, lo, hi)
        own = any(a < x[6] < b for a, b in sA)
        out.append((idx, len(k6A), len(k6B), len(sA), len(sAB), own, sAB[:3]))
    return out

if __name__ == '__main__':
    res = []
    with Pool(4) as pool:
        for J, step in ((1, 1), (2, 10)):
            d = pickle.load(open('cell_members7_J%d.pkl' % J, 'rb'))
            items = [(i, x) for i, x in d[::step]]
            chunks = [items[i:i + 400] for i in range(0, len(items), 400)]
            res.append((J, [r for c in pool.map(work, chunks) for r in c]))
    out = open('nesting_overlap_v1.out', 'w'); out.write(__doc__ + "\n")
    for J, rr in res:
        out.write("J=%d: crossers %d; own rho7 inside the [1,7]-nesting set in all: %s; crossers whose six admit a rho7 nesting BOTH windows: %d\n" % (
            J, len(rr), all(r[5] for r in rr), sum(1 for r in rr if r[4] > 0)))
        for r in rr:
            if r[4] > 0:
                out.write("   member %d: K6 windows %d, K'6 windows %d, [1,7]-set pieces %d, both-set pieces %d, e.g. %s\n" % (
                    r[0], r[1], r[2], r[3], r[4], [(float(a), float(b)) for a, b in r[6]]))
    out.close(); print(open('nesting_overlap_v1.out').read()[len(__doc__):])
