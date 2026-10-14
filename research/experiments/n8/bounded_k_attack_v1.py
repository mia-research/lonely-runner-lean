"""Adversarial attack on: for every ds there is a flank e and an opening k <= K0 that is lonely.

small_k_theorem_v1 found 100% coverage at K = 20 using ANY flank, across real, integer and
small-denominator sets. If that holds with a provable K0 it reduces ExistenceAt8 to a
BOUNDED search, which is a far more tractable statement than 'the cascade terminates'.

So this tries to BREAK it: hill-climb on ds to MAXIMISE the smallest k that works at any
flank. A confirmation run would be worthless here.
"""
import random
from fractions import Fraction as F

def circd(x):
    f = x - (x.numerator // x.denominator)
    return min(f, 1 - f)

def min_k_any_flank(ds, KMAX=4000):
    for k in range(KMAX + 1):
        for e in ds:
            t = (F(k) + F(1, 8)) / e
            if all(circd(d * t) >= F(1, 8) for d in ds):
                return k
    return None

rng = random.Random(1)
def perturb(ds, scale):
    out = list(ds)
    i = rng.randrange(len(out))
    delta = F(rng.randint(-scale, scale), 1000)
    cand = out[i] + delta
    if cand <= 0: return None
    out[i] = cand
    return sorted(set(out)) if len(set(out)) == len(ds) else None

best = (0, None)
hist = {}
for restart in range(300):
    kind = restart % 3
    if kind == 0:
        ds = sorted({F(rng.randint(1, 200000), 1000) for _ in range(7)})
    elif kind == 1:
        ds = sorted(F(x) for x in rng.sample(range(1, 300), 7))
    else:
        ds = sorted({F(rng.randint(1, 80), rng.choice([1,2,3,4,6,8,12])) for _ in range(7)})
    if len(ds) != 7: continue
    cur = min_k_any_flank(ds)
    if cur is None: cur = 10**9
    for step in range(120):
        cand = perturb(ds, 4000 if kind == 0 else 800)
        if cand is None or len(cand) != 7: continue
        v = min_k_any_flank(cand)
        v = 10**9 if v is None else v
        if v >= cur:
            ds, cur = cand, v
    hist[min(cur, 100)] = hist.get(min(cur, 100), 0) + 1
    if cur > best[0]:
        best = (cur, list(ds))

print(f"hill-climb restarts maximising the smallest working k : 300")
print(f"largest smallest-k reached                            : {best[0]}")
print(f"distribution of final k (capped at 100)               : {dict(sorted(hist.items()))}")
if best[1] and best[0] < 10**9:
    print(f"\nworst set found (k = {best[0]}):")
    print(f"  {[str(x) for x in best[1]]}")
    print(f"  normalised by d_min: {[float(x/min(best[1])) for x in best[1]]}")
