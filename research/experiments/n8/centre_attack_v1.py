"""Constructive attack: is there always a solution near m/2?

For b | m:  if m/b is ODD, m/2 mod b = b/2 (dead centre, best possible).
            if m/b is EVEN, m/2 mod b = 0 (worst possible -- blocked).
So q = m/2 + delta, and delta must clear the even-quotient moduli.  How big must delta be?
"""
from itertools import combinations

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def ok(q, m, bs):
    return all(I(b)[0] <= q % b <= I(b)[1] for b in bs + [m])

worst = 0; warg = None; tot = 0; dists = []
for m in range(24, 320):
    ds = [d for d in range(1, m+1) if m % d == 0]
    if len(ds) < 7: continue
    mid = [d for d in ds if d != 1 and d != m]
    for c in combinations(mid, 5):
        bs = sorted(m//s for s in c)
        tot += 1
        c0 = m // 2
        best = None
        for d in range(0, m//2 + 1):
            for q in (c0 + d, c0 - d):
                if 0 <= q < m and ok(q, m, bs):
                    best = d; break
            if best is not None: break
        dists.append((best, m, bs))
        if best is not None and best/m > worst:
            worst, warg = best/m, (m, bs, best)
import statistics
ds_ = [d for d,_,_ in dists if d is not None]
print(f"divisor-closed, exhaustive m < 320 : {tot:,}")
print(f"  profiles with NO solution anywhere: {sum(1 for d,_,_ in dists if d is None)}")
print(f"  |q - m/2| as a fraction of m : max {worst:.4f}  median {statistics.median(d/1 for d in ds_):.1f} (abs)")
print(f"     worst case: m={warg[0]}  b={warg[1]}  needed offset {warg[2]}  = {warg[2]/warg[0]:.4f} m")
# how often does a SMALL fixed offset rule work?
for cap in (1, 2, 3, 4, 8, 16):
    n = sum(1 for d,_,_ in dists if d is not None and d <= cap)
    print(f"  offset <= {cap:<3} suffices for {100*n/tot:6.2f}% of profiles")
# what is the max offset in ABSOLUTE terms, and does it grow with m?
mx = {}
for d, m, bs in dists:
    if d is None: continue
    mx[m] = max(mx.get(m, 0), d)
big = sorted(mx.items())[-6:]
print(f"  largest offset needed, by m (last 6): {big}")
