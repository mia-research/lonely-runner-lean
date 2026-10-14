"""Is 3/7 a genuine global floor for the conditional density, and does the product bound hold?"""
from fractions import Fraction as F
from itertools import combinations
import random

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def cond(b, bp):
    lo, hi = I(bp); lo2, hi2 = I(b)
    return F(sum(1 for r in range(lo, hi+1) if lo2 <= r % b <= hi2), hi-lo+1)

# 1. floor over a much larger range (sampled b', all divisors b)
rng = random.Random(20260919)
mn = None; marg = None; n = 0
for bp in list(range(2, 400)) + rng.sample(range(400, 60000), 1200):
    for b in range(2, min(bp, 400)):
        if bp % b: continue
        c = cond(b, bp); n += 1
        if mn is None or c < mn: mn, marg = c, (b, bp)
print(f"1. conditional density over {n:,} divisor pairs (b' up to 60,000)")
print(f"   minimum {mn} = {float(mn):.6f}  at b={marg[0]}, b'={marg[1]}   (3/7 = {float(F(3,7)):.6f})")
print(f"   is the min exactly 3/7 ? {mn == F(3,7)}")

# 2. does the crude product bound hold for chain profiles?
def chains(m):
    ds = sorted(d for d in range(2, m) if m % d == 0); out = []
    def go(p):
        if len(p) == 5: out.append(tuple(p)); return
        last = p[-1] if p else 1
        for d in ds:
            if d > last and d % last == 0: go(p+[d])
    go([]); return out
def density(m, bs):
    cnd = [(b,)+I(b) for b in bs] + [(m,)+I(m)]
    return F(sum(1 for q in range(m) if all(lo<=q%b<=hi for b,lo,hi in cnd)), m)

bound = F(3,4) * F(3,7)**5
print(f"\n2. crude product bound  (|I(m)|/m ~ 3/4) x (3/7)^5 = {float(bound):.6f}")
worst = None; tot = 0; viol = 0
for m in range(24, 800):
    for ch in chains(m):
        d = density(m, list(ch)); tot += 1
        if d < bound: viol += 1
        if worst is None or d < worst[0]: worst = (d, m, ch)
print(f"   chain profiles m < 800 : {tot:,}   density below the bound: {viol}")
print(f"   observed minimum density {worst[0]} = {float(worst[0]):.6f}  at m={worst[1]} chain={worst[2]}")
print(f"   headroom: observed min is {float(worst[0]/bound):.1f}x the crude bound")
print(f"\n   density x m >= 1 needs m >= {int(1/float(bound))+1} for the crude bound;")
print(f"   with the observed min {float(worst[0]):.4f}, m >= {int(1/float(worst[0]))+1}")
