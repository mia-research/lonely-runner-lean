"""Owner: no arrangement can move so that it is not isolated; scale invariance and the neighbour bounds mean every
arrangement just pushes the isolation.  Track each lonely stretch of the slowest runner along the deformation paths of
pinchoff_v1, in the scale-free coordinate R = 8 d_min t (only the ratios rho_j = d_j/d_min matter; runner j holds the
slot on R in ((8k-1)/rho_j, (8k+1)/rho_j)).  Exact (Fraction), BSM.
A stretch is labelled by its ends: left = the zone exit that opens it (runner, lap), right = the zone entry that closes
it (runner, lap); the window is R in [1, 15] (left end at R = 1 is runner 0's lap-0 exit, the bound).
Between consecutive grid points a stretch continues if the next grid point has a stretch with the same left or the same
right label (a hand-off changes one label at a time); otherwise it pinched off.  Unmatched new stretches are births.
Recorded per path: births, pinch-offs, ambiguous matches (both labels changed in one step: flagged, not guessed), the
fewest stretches at any grid point, and the LINEAGE of the stretch holding the event: whether the target's isolation
at s = 1 descends, through hand-offs only, from a stretch present just after the progression (s = 1/N)."""
import sys
from fractions import Fraction as F
from math import floor, ceil
from pinchoff_v1 import targets, readings_at, EIGHTH

RMAX = 15

def stretches(ds):
    rho = [d / ds[0] for d in ds]
    Z = []
    for j, r in enumerate(rho):
        for k in range(0, ceil((RMAX * r + 1) / 8) + 1):
            lo, hi = F(8 * k - 1) / r, F(8 * k + 1) / r
            if hi > 1 and lo < RMAX: Z.append((lo, hi, j, k))
    Z.sort()
    out = []; cur = F(1); curlab = (0, 0)
    for lo, hi, j, k in Z:
        if hi <= cur:
            continue
        if lo >= cur and lo <= RMAX:
            out.append((cur, lo, curlab, (j, k)))
        if hi > cur:
            cur, curlab = hi, (j, k)
        if cur > RMAX: break
    if cur <= RMAX: out.append((cur, F(RMAX), curlab, ('W', 0)))
    return out

def track(args):
    name, V, N = args
    D1 = [F(v - V[0]) for v in V[1:]]; W = D1[-1]; D0 = [W * j / 7 for j in range(1, 8)]
    prev = None; lineage = None; births = pinches = amb = 0; fewest = None; handoffs = 0
    root_ids = None; nid = 0; ids_prev = []
    for i in range(1, N + 1):
        s = F(i, N); S = stretches(readings_at(D0, D1, s))
        fewest = len(S) if fewest is None else min(fewest, len(S))
        if prev is None:
            ids = list(range(len(S))); nid = len(S); root_ids = set(ids)
        else:
            ids = []
            used = set()
            for (a, b, L, Rt) in S:
                m = [q for q, (a0, b0, L0, R0) in enumerate(prev) if L0 == L or R0 == Rt]
                m = [q for q in m if q not in used]
                if len(m) == 1:
                    ids.append(ids_prev[m[0]]); used.add(m[0])
                    if (prev[m[0]][2], prev[m[0]][3]) != (L, Rt): handoffs += 1
                elif len(m) > 1:
                    amb += 1; ids.append(ids_prev[m[0]]); used.add(m[0])
                else:
                    births += 1; ids.append(nid); nid += 1
            pinches += len(prev) - len(used)
        prev, ids_prev = S, ids
    # the event is the first stretch; its lineage id at s = 1
    ev_id = ids_prev[0]
    return name, V, births, pinches, handoffs, amb, fewest, ev_id in root_ids, sorted(set(ids_prev) & root_ids), len(root_ids)

if __name__ == '__main__':
    from multiprocessing import Pool
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    T = [t for t in targets() if t[0].startswith('random') or 'W30' in t[0]]
    with Pool() as pool:
        res = pool.map(track, [(n, V, N) for n, V in T])
    tot = dict(b=0, p=0, h=0, a=0); desc = 0; fewest = []
    for name, V, b, p, h, a, f, evroot, surv, nroot in res:
        tot['b'] += b; tot['p'] += p; tot['h'] += h; tot['a'] += a; desc += evroot; fewest.append(f)
        print(f"{name:24s} V {V}: births {b:3d} pinch-offs {p:3d} hand-offs {h:4d} ambiguous {a:2d}; fewest stretches {f:2d}; "
              f"roots at s=1/N {nroot:2d}, surviving to s=1 {len(surv):2d}; event descends from a root: {evroot}")
    print(f"\npaths {len(res)} (grid {N}): births {tot['b']}, pinch-offs {tot['p']}, hand-offs {tot['h']}, ambiguous {tot['a']}; "
          f"fewest stretches in R [1,{RMAX}] on any path {min(fewest)}; the target's isolation descends from a stretch present "
          f"just after the progression on {desc} of {len(res)} paths")
