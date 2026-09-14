"""n=6: find arrangements where the nearest runner is in the way at an iterate; trace the chain and check the first
isolation time independently by BSM (all zone endpoints; entry and exit values; boundary points evaluated separately)."""
from fractions import Fraction as F
import math, random
import importlib.util, sys, os
n = 6; th = F(1, n)
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
def chain(ds):
    t = th / ds[0]; its = []
    while True:
        inw = [i for i, d in enumerate(ds) if cd(d * t) < th]
        best = t; who = None
        for i in inw:
            d = ds[i]; k = math.ceil(d * t - th); o = (k + th) / d
            if o > best: best, who = o, (i, k)
        its.append((t, inw, who))
        if who is None: return its
        t = best
def lonely(ds, t): return all(cd(d * t) >= th for d in ds)
def bsm_first(ds, T):
    # candidate points: all zone ends (k + th)/d and zone starts (k - th)/d in (0, T]; lonely set is a union of closed
    # intervals whose left ends are zone ends (or 0); the first lonely positive time is the smallest candidate that is lonely
    cands = set()
    for d in ds:
        for k in range(0, math.ceil(d * T) + 2):
            for e in (k + th, k - th):
                x = e / d
                if 0 < x <= T: cands.add(x)
    for x in sorted(cands):
        if lonely(ds, x): return x
    return None
rng = random.Random(606)
found = []
for trial in range(400000):
    r = sorted(1 + F(rng.randint(0, 6000), 1000) for _ in range(4))
    if len(set(r)) < 4: continue
    ds = [F(1)] + r
    its = chain(ds)
    if any(0 in inw for _, inw, _ in its):
        found.append((n * its[-1][0], ds, its))
        if len(found) >= 40: break
print('trials', trial + 1, 'arrangements with the nearest runner in the way:', len(found))
found.sort(key=lambda x: -x[0])
for G, ds, its in found[:3]:
    T = its[-1][0]
    b = bsm_first(ds, T)
    print(f'\nratios {[str(x) for x in ds]}  final reading {float(G):.4f}  chain time {T}  BSM first lonely {b}  agree {b == T}')
    for j, (t, inw, who) in enumerate(its):
        print(f'   iterate {j}: nearest reading {float(n*t):.4f}  in the way {inw}  next setter {who}')
