"""REDO item 1 (supersedes tight_search_v1/v2, which enumerated one runner's difference set with that
runner at speed 0): runners that are lonely only at ISOLATED instants, found on arrangements.

Arrangements: all 8-element subsets of [1,B] (distinct positive speeds) with gcd of differences 1.
EVERY runner is evaluated in its own readings |v_j - v_k|.  Exact: the readings are integers, so the
lonely set has period 1; its complement on [0,1] is the union of the open zones ((8m-1)/(8d), (8m+1)/(8d)),
computed over the common denominator 8L, L = lcm of the readings, as integers.  Touching zones leave
their shared endpoint clear (BSM).  A runner is ISOLATED when its lonely set is nonempty and contains no
interval.  Reported per isolated runner: its lonely instants, the pinners (readings exactly 1/8 ahead and
7/8), the cascade's isolation event and tier, the arrangement's reduced residues mod 8.
"""
import sys, time
from itertools import combinations
from math import gcd, lcm
from functools import reduce
from multiprocessing import Pool
from arrangement_lib import readings, cascade, tier, reduced_residues, is_grid, F
B = int(sys.argv[1]) if len(sys.argv) > 1 else 20
def lonely_components(ds):
    L = reduce(lcm, ds); M = 8 * L
    z = sorted(((8 * m - 1) * (L // d), (8 * m + 1) * (L // d)) for d in ds for m in range(0, d + 1))
    comps = []; cur = 0
    for a, b in z:
        if a > cur: comps.append((cur, a))
        elif a == cur and cur > 0: comps.append((cur, cur))
        cur = max(cur, b)
    return [(F(a, M), F(b, M)) for a, b in comps if 0 < a and b < M]
def work(first):
    out = []; n_arr = n_run = 0
    for rest in combinations(range(first + 1, B + 1), 7):
        V = (first,) + rest
        if reduce(gcd, [v - first for v in rest]) != 1: continue
        n_arr += 1
        for k in range(8):
            n_run += 1
            c = lonely_components(readings(V, k))
            if not c: out.append((V, k, 'NOT LONELY', None))
            elif all(a == b for a, b in c): out.append((V, k, sorted({a for a, _ in c}), None))
    return n_arr, n_run, out
if __name__ == "__main__":
    t0 = time.time()
    with Pool(8) as p: parts = p.map(work, range(1, B - 6))
    n_arr = sum(x[0] for x in parts); n_run = sum(x[1] for x in parts); found = [o for x in parts for o in x[2]]
    notl = [f for f in found if f[2] == 'NOT LONELY']; iso = [f for f in found if f[2] != 'NOT LONELY']
    print(f"arrangements of 8 distinct speeds in [1,{B}], gcd of differences 1: {n_arr};  runners evaluated: {n_run}  ({time.time() - t0:.0f}s)")
    print(f"runners with no lonely instant: {len(notl)};  runners lonely only at isolated instants: {len(iso)}")
    shapes = {}
    for V, k, pts, _ in iso:
        ds = readings(V, k)
        key = tuple(ds)
        shapes.setdefault(key, []).append((V, k, pts))
    print(f"distinct reading sets among the isolated runners: {len(shapes)}")
    for key, lst in sorted(shapes.items()):
        V, k, pts = lst[0]
        t, m = cascade(list(key))
        pin_ahead = [d for d in key if (d * pts[0]) % 1 == F(1, 8)]; pin_behind = [d for d in key if (d * pts[0]) % 1 == F(7, 8)]
        print(f"  readings {list(key)}: {len(lst)} runner(s), e.g. runner at speed {V[k]} of {V} (grid mod 8: {is_grid(V)}, reduced residues {reduced_residues(V)})")
        print(f"     lonely only at {[str(p) for p in pts]};  at {pts[0]}: pinned ahead by {pin_ahead}, behind by {pin_behind};  cascade: t = {t} after {m} moves, tier {tier(V, k)}")
