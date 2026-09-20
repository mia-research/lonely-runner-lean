"""DoorFirstLap searched in the right region: ratios just ABOVE the ratio condition.

tau = e*t with e = least disparity.  tau > 1 means the cascade runs past the least runner's
first lap, which needs the least runner blocked repeatedly -- so the ratios d/e must be
MODERATE, not huge.  Theorem 4.8 says d_max <= (n-1)*d_min is settled at once (tau = 1/n).
The recorded n=8 witness {49,205,234,256,286,323,366} has d_max/d_min = 366/49 = 7.47,
just above 7 = n-1.  So the live region is ratios a little over n-1.
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

random.seed(4242)
print(f"{'n':>3} {'tested':>7} {'max tau':>10} {'moves':>6}  tau>1  witness")
for N in [5, 6, 7, 8]:
    casc = mk(N); k = N - 1
    worst, wset, wmv, found, tested = F(0), None, 0, 0, 0
    for _ in range(60000):
        e = random.randint(10, 400)
        top = int(e * (N - 1) * random.uniform(1.0, 1.6))
        if top <= e + k: continue
        rest = sorted(random.sample(range(e+1, top+1), k-1))
        c = (e, *rest)
        g = c[0]
        for x in c[1:]: g = math.gcd(g, x)
        if g != 1: continue
        ds = [F(x) for x in c]
        tested += 1
        t, mv = casc(ds)
        if t is None: continue
        tau = min(ds) * t
        if tau > 1: found += 1
        if tau > worst: worst, wset, wmv = tau, c, mv
    flag = f"YES ({found})" if found else "no"
    print(f"{N:>3} {tested:>7} {float(worst):>10.5f} {wmv:>6}  {flag}  {wset}")
    if found: print(f"        -> REFUTED at n={N}: tau = {worst} > 1")
