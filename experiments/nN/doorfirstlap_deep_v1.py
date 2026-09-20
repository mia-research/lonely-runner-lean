"""DoorFirstLap at n=5,6,7 searched by DEPTH, not by random difference sets.

Random sampling misses the known n=8 witness even at 40k draws (doorfirstlap_nN_v1.out), so it
is not a usable instrument.  The recorded n=8 counterexample is the 28-move adversarial case:
depth is what produces large tau.  This searches the deep families found in n5_movecount_v1.
"""
import math, random
from fractions import Fraction as F

def mk(N):
    INV = F(1, N)
    def circDist(x):
        fr = x - math.floor(x); return min(fr, 1 - fr)
    def inWay(d, t): return circDist(d*t) < INV
    def nextOpening(d, t): return (F(math.ceil(d*t - INV)) + INV)/d
    def cascade(ds, cap=300000):
        a = min(ds); t = F(1,1)/(N*a); m = 0
        for _ in range(cap):
            act = [d for d in ds if inWay(d, t)]
            if not act: return t, m
            t = max(nextOpening(d, t) for d in act); m += 1
        return None, cap
    return cascade

# control
c8 = mk(8); t, mv = c8([F(x) for x in (49,205,234,256,286,323,364+2)])
print(f"control n=8 witness: tau = {min([F(49)])*t} in {mv} moves  (expect 2401/1872, 28 moves)")
print()

random.seed(2026)
print("=== deep families: tau = leastDisp * arrival ===")
print(f"{'n':>3} {'tested':>7} {'max moves':>10} {'max tau':>12}   tau>1 found   witness")
for N in [5, 6, 7, 8]:
    casc = mk(N); k = N - 1
    worst, wset, deepest, found, tested = F(0), None, 0, 0, 0
    for _ in range(12000):
        M = random.choice([10**4, 10**5, 10**6, 10**7, 10**8])
        lo = random.choice([1, 2, 3])
        rest = sorted(random.sample(range(M, M + M//30 + 2), k-1))
        c = (lo, *rest)
        g = c[0]
        for x in c[1:]: g = math.gcd(g, x)
        if g != 1: continue
        ds = [F(x) for x in c]
        tested += 1
        t, mv = casc(ds)
        if t is None: continue
        deepest = max(deepest, mv)
        tau = min(ds) * t
        if tau > 1: found += 1
        if tau > worst: worst, wset = tau, c
    flag = f"YES ({found})" if found else "no"
    print(f"{N:>3} {tested:>7} {deepest:>10} {float(worst):>12.5f}   {flag:>12}   {wset}")
