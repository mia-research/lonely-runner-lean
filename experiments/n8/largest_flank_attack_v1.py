"""CLAIM: the flank at a subject's largest |difference| is always clear.  If true, that is Existence.
Sampling said 100% of 48,000.  Attack it: hill-climb to maximise the first-clear index, and
hunt structured arrangements (APs, geometric, near-degenerate, half-integer heavy)."""
from fractions import Fraction as F
import random

def frac(r): return r - (r.numerator // r.denominator)

def largest_flank_first_clear(v, i, kmax=20000):
    ds = [v[j] - v[i] for j in range(len(v)) if j != i]
    e = max(ds, key=abs); ae = abs(e)
    ratios = [F(d, ae) for d in ds]
    if any(r.denominator == 1 and r.numerator % 8 == 0 for r in ratios): return 'dead'
    movers = [r for r in ratios if r.denominator != 1]
    for k in range(kmax):
        ok = True
        for r in movers:
            x = k*frac(r) + r/8
            if abs(x - F(round(float(x)))) < F(1,8): ok = False; break
        if ok: return k
    return None

rng = random.Random(20260919)
worst = (-1, None, None)
# 1. hill-climb to maximise the first-clear index of the largest flank
for restart in range(80):
    v = sorted(rng.sample(range(0, 300), 8)); i = rng.randrange(8)
    cur = largest_flank_first_clear(v, i)
    if cur in ('dead', None): cur = -1 if cur == 'dead' else 10**9
    for _ in range(300):
        w = list(v); j = rng.randrange(8)
        w[j] += rng.choice([-4,-3,-2,-1,1,2,3,4])
        if len(set(w)) != 8 or min(w) < 0: continue
        w = sorted(w)
        c = largest_flank_first_clear(w, i)
        if c == None: cur = 10**9; v = w; break
        if c == 'dead': continue
        if c > cur: v, cur = w, c
    if cur > worst[0]: worst = (cur, list(v), i)
print(f"1. hill-climb, largest first-clear index of the largest flank: {worst[0]}")
print(f"   at {worst[1]}, subject {worst[2]}")

# 2. structured families
print(f"\n2. structured arrangements:")
fams = {
 "AP":            [[a + d*t for t in range(8)] for a in (0,1,3) for d in (1,2,3,5,7,8)],
 "geometric-ish": [[a*(t+1)**2 for t in range(8)] for a in (1,2,3)],
 "powers of 2":   [[a*2**t for t in range(8)] for a in (1,3)],
 "near-equal":    [[100, 101, 102, 103, 104, 105, 106, 107+g] for g in (1,2,4,8,16)],
 "half-heavy":    [[0, 2, 4, 6, 8, 10, 12, 14+o] for o in (1,3,5,7)],
}
bad = 0
for name, arrs in fams.items():
    for v in arrs:
        v = sorted(set(v))
        if len(v) != 8: continue
        for i in range(8):
            r = largest_flank_first_clear(v, i)
            if r is None:
                bad += 1; print(f"   SHADOWED: {name} {v} subject {i}")
print(f"   structured families: largest flank shadowed in {bad} cases")
