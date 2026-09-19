"""Fully native: no reals, no rounding, no LRC import.

By divisor_reduces + small_b_blocks_iff, a divisor-closed profile is clear iff there is an integer q
with   q mod b_i  in  I(b_i) = [ceil((b_i-1)/8), floor((7 b_i -1)/8)]   for each b_i = m/s_i,
INCLUDING b = m (which is exactly the admissible range).  All moduli divide m, so everything is
decided by q mod m.  Count the solutions exactly.
"""
from itertools import combinations
from fractions import Fraction as F

def I(b): return (-(-(b-1)//8), (7*b-1)//8)

def solutions(m, bs):
    lo_hi = [(b,)+I(b) for b in bs] + [(m,)+I(m)]
    return [q for q in range(m) if all(lo <= q % b <= hi for b, lo, hi in lo_hi)]

tot = 0; zero = 0; mn = None; mnarg = None
dens = []
for m in range(24, 320):
    ds = [d for d in range(1, m+1) if m % d == 0]
    if len(ds) < 7: continue
    mid = [d for d in ds if d != 1 and d != m]
    for c in combinations(mid, 5):
        bs = [m//s for s in c]
        sol = solutions(m, bs)
        tot += 1
        if not sol:
            zero += 1
            if mnarg is None: mnarg = (m, sorted(bs))
        d = F(len(sol), m)
        dens.append(d)
        if mn is None or d < mn: mn, cand = d, (m, sorted(bs), len(sol))
print(f"DIVISOR-CLOSED, exhaustive m < 320 : {tot:,} profiles   (no reals used)")
print(f"  profiles with NO solution q       : {zero:,}")
print(f"  minimum solution DENSITY          : {mn} = {float(mn):.6f}   at m={cand[0]} b={cand[1]}"
      f"  ({cand[2]} solutions)")
import statistics
f = [float(x) for x in dens]
print(f"  density: min {min(f):.4f}  median {statistics.median(f):.4f}  max {max(f):.4f}")
print(f"  naive independent estimate (3/4)^5 = {0.75**5:.4f}")
# smallest absolute solution count
cnts = []
for m in range(24, 320):
    ds = [d for d in range(1, m+1) if m % d == 0]
    if len(ds) < 7: continue
    mid = [d for d in ds if d != 1 and d != m]
    for c in combinations(mid, 5):
        cnts.append(len(solutions(m, [m//s for s in c])))
print(f"\n  smallest number of solutions over all profiles: {min(cnts)}")
