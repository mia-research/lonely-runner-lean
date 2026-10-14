"""Does the free density (= solution density) have a positive floor, or decay to 0?
If a positive floor is provable, existence follows.  Chains gave >= 0.10; general divisor-closed
gave 1/45 at m < 320.  Push the range hard and find the infimum and where it sits."""
from itertools import combinations
from fractions import Fraction as F
import random

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def density(m, bs):
    cond = [(b,)+I(b) for b in bs] + [(m,)+I(m)]
    n = sum(1 for q in range(m) if all(lo <= q % b <= hi for b,lo,hi in cond))
    return F(n, m), n

rng = random.Random(20260919)
print(f"{'m range':<16} {'profiles':>8} {'min density':>13} {'min #sols':>10}  worst profile")
overall = None
for lo, hi in ((24,320),(320,1200),(1200,5000),(5000,20000)):
    mn = None; warg = None; tot = 0; zero = 0
    ms = [m for m in range(lo,hi) if sum(1 for d in range(1,m+1) if m%d==0) >= 7]
    if len(ms) > 150: ms = rng.sample(ms, 150)
    for m in ms:
        mid = [d for d in range(2,m) if m % d == 0]
        combos = list(combinations(mid,5))
        if len(combos) > 40: combos = rng.sample(combos, 40)
        for c in combos:
            bs = sorted(m//s for s in c); tot += 1
            d, n = density(m, bs)
            if n == 0: zero += 1
            if mn is None or d < mn: mn, warg = d, (m, bs, n)
    print(f"  [{lo:>5},{hi:>5})  {tot:>8} {str(mn):>13} {warg[2]:>10}  m={warg[0]} b={warg[1]}"
          + (f"   ZERO {zero}" if zero else ""))
    if overall is None or mn < overall[0]: overall = (mn, warg)
print(f"\n  overall minimum density {overall[0]} = {float(overall[0]):.6f}"
      f"   with {overall[1][2]} solutions   at m={overall[1][0]}")
print(f"  density x m = number of solutions; the floor question is whether that count can reach 0.")
