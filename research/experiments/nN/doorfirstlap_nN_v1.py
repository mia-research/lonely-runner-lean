"""DoorFirstLap at n = 5, 6, 7 -- with the known n=8 refutation as a POSITIVE CONTROL.

whatfails_v1.py's check 3 found no tau > 1 at n=8, where tau = 2401/1872 is RECORDED.  A sample
that cannot reproduce a known positive cannot license a null at any order, so that run is void.
This one first reproduces the n=8 witness, then searches the same SHAPE at 5, 6, 7:
a small least disparity against large ones, which is where fine denominators live.
"""
import math, random
from fractions import Fraction as F

def mk(N):
    INV = F(1, N)
    def circDist(x):
        fr = x - math.floor(x); return min(fr, 1 - fr)
    def inWay(d, t): return circDist(d*t) < INV
    def nextOpening(d, t): return (F(math.ceil(d*t - INV)) + INV)/d
    def cascade(ds, cap=200000):
        a = min(ds); t = F(1,1)/(N*a)
        for _ in range(cap):
            act = [d for d in ds if inWay(d, t)]
            if not act: return t
            t = max(nextOpening(d, t) for d in act)
        return None
    return cascade

print("=== POSITIVE CONTROL: the recorded n=8 refutation ===")
c8 = mk(8)
ds8 = [F(x) for x in (49, 205, 234, 256, 286, 323, 366)]
t8 = c8(ds8)
tau8 = min(ds8) * t8
print(f"  disparities {{49,205,234,256,286,323,366}}  arrival t = {t8}")
print(f"  tau = 49*t = {tau8} = {float(tau8):.5f}   expected 2401/1872 = 1.28259")
print(f"  CONTROL {'PASSES' if tau8 == F(2401,1872) else 'FAILS -- harness is wrong, stop'}")
print()

print("=== targeted search at n = 5, 6, 7 (same shape: small min, large spread) ===")
random.seed(99)
for N in [5, 6, 7, 8]:
    casc = mk(N); k = N - 1
    worst, wset, tested, found = F(0), None, 0, 0
    for _ in range(40000):
        style = random.random()
        if style < 0.5:
            lo = random.randint(1, 60)
            rest = sorted(random.sample(range(lo+1, lo*random.choice([8,12,20,40])+50), k-1))
        else:
            lo = random.randint(20, 300)
            rest = sorted(random.sample(range(lo+1, lo*random.choice([4,6,10])+20), k-1))
        c = (lo, *rest)
        if len(set(c)) != k: continue
        g = c[0]
        for x in c[1:]: g = math.gcd(g, x)
        if g != 1: continue
        ds = [F(x) for x in c]
        tested += 1
        t = casc(ds)
        if t is None: continue
        tau = min(ds) * t
        if tau > 1: found += 1
        if tau > worst: worst, wset = tau, c
    verdict = f"REFUTED at n={N} ({found} cases with tau>1)" if found else "no tau>1 in THIS sample"
    print(f"  n={N}  tested {tested:>6}   max tau {float(worst):>9.5f} = {worst}")
    print(f"        {verdict}   witness {wset}")
