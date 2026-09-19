"""Does the offset from m/2 stay bounded as m grows?  If yes, a constructive proof is in reach."""
from itertools import combinations
import random

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def ok(q, m, bs): return all(I(b)[0] <= q % b <= I(b)[1] for b in bs + [m])

def offset(m, bs):
    c0 = m // 2
    for d in range(0, m//2 + 1):
        for q in (c0 + d, c0 - d):
            if 0 <= q < m and ok(q, m, bs): return d
    return None

rng = random.Random(20260919)
print(f"{'m range':<18} {'profiles':>8} {'max offset':>11} {'max offset/m':>13}  worst")
for lo, hi in ((24,200),(200,1000),(1000,5000),(5000,20000),(20000,100000)):
    mx = 0; warg = None; tot = 0; none = 0
    ms = [m for m in range(lo, hi) if sum(1 for d in range(1,m+1) if m%d==0) >= 7]
    if len(ms) > 220: ms = rng.sample(ms, 220)
    for m in ms:
        ds = [d for d in range(1, m+1) if m % d == 0]
        mid = [d for d in ds if d != 1 and d != m]
        combos = list(combinations(mid, 5))
        if len(combos) > 60: combos = rng.sample(combos, 60)
        for c in combos:
            bs = sorted(m//s for s in c); tot += 1
            o = offset(m, bs)
            if o is None: none += 1; continue
            if o > mx: mx, warg = o, (m, bs)
    print(f"  [{lo:>6},{hi:>6})  {tot:>8} {mx:>11} {mx/max(warg[0],1):>13.5f}  m={warg[0]} b={warg[1]}"
          + (f"   NO-SOLUTION {none}" if none else ""))
