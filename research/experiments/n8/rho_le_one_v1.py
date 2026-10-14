"""The largest flank's distinguishing feature is ALL |rho_j| <= 1.
CLAIM: a flank with every |rho| <= 1 is clear.
Attack it in RATIO SPACE (not arrangement space) -- that is what caught the last error.
Construct 6 rationals in (-1,1) and look for a shadowing set."""
from fractions import Fraction as F
from itertools import product
import random

def shadowed(rhos, kmax=20000):
    for k in range(kmax):
        ok = True
        for r in rhos:
            x = r * (k + F(1,8))
            if abs(x - F(round(float(x)))) < F(1,8): ok = False; break
        if ok: return False
    return True

rng = random.Random(20260919)
# 1. exhaustive over small denominators
print("1. exhaustive: 6 ratios from +/- p/q with q <= 6, |rho| < 1")
cands = sorted({F(s*p, q) for q in range(2,7) for p in range(1,q) for s in (1,-1)})
print(f"   ratio pool size {len(cands)}")
found = []
for _ in range(200000):
    rhos = [rng.choice(cands) for _ in range(6)]
    if shadowed(rhos, kmax=400):
        if shadowed(rhos, kmax=20000): found.append(rhos)
        if len(found) >= 3: break
print(f"   shadowing sets found: {len(found)}")
for f in found[:3]: print(f"      {[str(x) for x in f]}")

# 2. adversarial: hill-climb to maximise first clear index
def first_clear(rhos, kmax=200000):
    for k in range(kmax):
        ok = True
        for r in rhos:
            x = r * (k + F(1,8))
            if abs(x - F(round(float(x)))) < F(1,8): ok = False; break
        if ok: return k
    return None
best = (-1, None)
for _ in range(40):
    rhos = [rng.choice(cands) for _ in range(6)]
    cur = first_clear(rhos, 20000)
    if cur is None: print(f"   SHADOWED by climb: {[str(x) for x in rhos]}"); break
    for _ in range(200):
        w = list(rhos); j = rng.randrange(6); w[j] = rng.choice(cands)
        c = first_clear(w, 20000)
        if c is None: rhos = w; cur = 10**9; break
        if c > cur: rhos, cur = w, c
    if cur > best[0]: best = (cur, list(rhos))
print(f"\n2. adversarial max first-clear index: {best[0]}")
print(f"   at {[str(x) for x in best[1]] if best[1] else '-'}")
