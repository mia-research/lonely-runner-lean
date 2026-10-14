"""Random sampling gives min 3 clear flanks per subject.  Sampling misled twice already.
Hill-climb to MINIMISE the clear-flank count for a subject -- the adversarial search."""
from fractions import Fraction as F
import random

def frac(r): return r - (r.numerator // r.denominator)

def clear_count(v, i, kmax=400):
    ds = [v[j] - v[i] for j in range(len(v)) if j != i]
    n = 0
    for e in ds:
        if e == 0: continue
        ratios = [F(d, abs(e)) for d in ds]
        if any(r.denominator == 1 and r.numerator % 8 == 0 for r in ratios): continue
        movers = [r for r in ratios if r.denominator != 1]
        for k in range(kmax):
            ok = True
            for r in movers:
                x = k*frac(r) + r/8
                if abs(x - F(round(float(x)))) < F(1,8): ok = False; break
            if ok: n += 1; break
    return n

rng = random.Random(20260919)
best = (99, None, None)
for restart in range(60):
    v = sorted(rng.sample(range(0, 200), 8))
    i = rng.randrange(8)
    cur = clear_count(v, i)
    for _ in range(400):
        w = list(v); j = rng.randrange(8)
        w[j] += rng.choice([-5,-3,-2,-1,1,2,3,5])
        if len(set(w)) != 8 or min(w) < 0: continue
        w = sorted(w)
        c = clear_count(w, i)
        if c <= cur: v, cur = w, c
        if cur == 0: break
    if cur < best[0]: best = (cur, list(v), i)
    if best[0] == 0: break
print(f"adversarial minimisation of clear-flank count")
print(f"  best found: {best[0]} clear flanks (of 7)")
print(f"  arrangement {best[1]}, subject {best[2]}")
print(f"\n  a subject with 0 clear flanks would be a counterexample to LRC at n = 8.")
print(f"  minimum reached: {best[0]}")
