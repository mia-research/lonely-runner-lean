"""The ideal (global isolation) as a reference for the order-eight residual.

At the ideal, disparities D, 2D, ..., 7D, the four global instants a/(8D), a = 1, 3, 5, 7, pinch the
subject's lonely set to a point: runner aD opens (a*a = 1 mod 8) and runner (8-a)D closes
(a*(8-a) = -1 mod 8), the rest sit on vertices with slack 1/8.  Events a and 8-a use the same pair
with the roles swapped, so a small deformation opens one of them and closes the other.

Reports: delta(S) = max_t min_d ||d t|| (exact, over mirror meetings k/(d+d') and equal meetings
k/|d-d'|) on the v1 residual of [1,30] and [1,40]; then, by rank pair, how often some mirror
meeting k/(d+d') is lonely at 1/8.
"""
import itertools, random, time
from fractions import Fraction as Fr
from collections import Counter
from math import gcd
_rs = __file__.replace('ideal_events_v1.py', 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])
def delta(S):
    """exact max_t min_d ||d t|| over t in (0,1), at mirror meetings k/(d+d') and equal meetings k/|d-d'|"""
    best = (Fr(-1), None)
    for d, d2 in itertools.combinations(S, 2):
        for m, sign in ((d + d2, '+'), (abs(d - d2), '-')):
            if m == 0: continue
            for k in range(1, m):
                if gcd(k, m) != 1: continue
                v = min(min(x * k % m, m - x * k % m) for x in S)
                val = Fr(v, m)
                if val > best[0]: best = (val, (d, d2, sign, k, m))
    return best
def near_small_q(k, m):
    """closest i/q, q <= 8, to t = k/m, as (distance * 8 * max... ) -> return (q, i, |t - i/q|)"""
    t = Fr(k, m); return min(((q, i, abs(t - Fr(i, q))) for q in range(1, 9) for i in range(q + 1)), key=lambda x: x[2])
for top in (30, 40):
    t0 = time.time(); n = 0; below = []; mn = None; at7 = 0
    for S in itertools.combinations(range(1, top + 1), 7):
        if not eight_residual(S): continue
        n += 1
        v, w = delta(S)
        if mn is None or v < mn[0]: mn = (v, S, w)
        if v < Fr(1, 7): below.append((v, S, w))
        at7 += (v == Fr(1, 7))
    print(f"[1,{top}] residual v1 {n}: min delta {mn[0]} at {mn[1]} (t* = {mn[2][3]}/{mn[2][4]});  sets with delta < 1/7: {len(below)};  delta exactly 1/7: {at7}  ({time.time()-t0:.0f}s)")
    for v, S, w in sorted(below)[:8]: print("    ", S, v, f"t* = {w[3]}/{w[4]}")

def lonely_mirror(S, d, d2):
    m = d + d2
    return [k for k in range(1, m) if all(m <= 8 * (x * k % m) <= 7 * m for x in S)]
for top, samp in ((30, None), (40, 6000)):
    R = [S for S in itertools.combinations(range(1, top + 1), 7) if eight_residual(S)]
    if samp: random.seed(6); R = random.sample(R, samp)
    t0 = time.time(); by = Counter(); anyp = 0; ideal_pairs = 0
    for S in R:
        s = sorted(S); hit = set()
        for r1, r2 in itertools.combinations(range(7), 2):
            if lonely_mirror(S, s[r1], s[r2]): hit.add((r1 + 1, r2 + 1))
        for p in hit: by[p] += 1
        anyp += bool(hit); ideal_pairs += bool(hit & {(1, 7), (3, 5)})
    print(f"[1,{top}] residual v1 ({len(R)} sets{' sampled' if samp else ''}): lonely at some mirror meeting k/(d+d'): {anyp};  at an ideal pair (1,7) or (3,5): {ideal_pairs}  ({time.time()-t0:.0f}s)")
    print("   by rank pair (share of sets):", " ".join(f"{p}:{by[p]/len(R):.2f}" for p in sorted(by, key=lambda p: -by[p])))
