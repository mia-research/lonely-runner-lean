"""Why does the rule work at b >= 8 when the margin argument only gives b >= 28?

The admissible tau = (8q+1)/(8m) are spaced 1/m apart.  A clear component of width > 1/m must
contain one.  So measure the clear set of {tau : ||s tau|| >= 1/8 for s in {1,s_1..s_5}} exactly,
and compare its widest component with 1/m.
"""
from fractions import Fraction as F
from itertools import combinations

def clear_components(speeds):
    """Exact clear set inside [0,1] for threshold 1/8, as a list of (lo,hi)."""
    bad = []
    for s in speeds:
        k = 0
        while F(8*k - 1, 8*s) < 1:
            lo, hi = F(8*k-1, 8*s), F(8*k+1, 8*s)
            if hi > 0 and lo < 1: bad.append((max(lo, F(0)), min(hi, F(1))))
            k += 1
    bad.sort()
    merged = []
    for a, b in bad:
        if merged and a <= merged[-1][1]: merged[-1] = (merged[-1][0], max(merged[-1][1], b))
        else: merged.append((a, b))
    comps, cur = [], F(0)
    for a, b in merged:
        if a > cur: comps.append((cur, a))
        cur = max(cur, b)
    if cur < 1: comps.append((cur, F(1)))
    return comps

rows = []
for m in range(24, 200):
    ds = [d for d in range(1, m+1) if m % d == 0]
    if len(ds) < 7: continue
    mid = [d for d in ds if d != 1 and d != m]
    for c in combinations(mid, 5):
        comps = clear_components([1] + list(c))
        w = max((b-a for a, b in comps), default=F(0))
        bs = sorted(m//s for s in c)
        rows.append((m, bs, w, F(1, m)))
tot = len(rows)
wide = sum(1 for _,_,w,g in rows if w >= g)
print(f"divisor-closed profiles, m < 200 : {tot:,}")
print(f"  widest clear component >= 1/m  : {wide:,}  ({100*wide/tot:.2f}%)")
print(f"  widest clear component <  1/m  : {tot-wide:,}\n")
narrow = [(m,bs,w,g) for m,bs,w,g in rows if w < g]
for m,bs,w,g in narrow[:6]:
    print(f"    m={m:<4} b={bs}   widest {w} = {float(w):.6f}   1/m = {float(g):.6f}")
# ratio distribution
import statistics
rat = [float(w*m) for m,_,w,_ in rows]
print(f"\n  ratio (widest component)/(1/m):  min {min(rat):.3f}  "
      f"median {statistics.median(rat):.3f}  max {max(rat):.3f}")
