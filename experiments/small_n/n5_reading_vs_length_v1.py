"""n=5: largest final nearest reading by chain length and by the smallest lap any setter used (random, near-rational,
near-AP generators)."""
from fractions import Fraction as F
import math, random, collections
n = 5; th = F(1, n)
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
def chain(ds):
    t = th / ds[0]; steps = []
    while True:
        best = t; who = None
        for i, d in enumerate(ds):
            if cd(d * t) < th:
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, (i, k)
        if who is None: return steps, t
        steps.append(who); t = best
rng = random.Random(13)
RATS = [F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3), F(4)]
bylen = collections.defaultdict(F); bymaxlap = collections.defaultdict(F); cnt = 0
def gen():
    for _ in range(80000):
        M = rng.choice([4, 10, 30, 100])
        yield sorted(1 + F(rng.randint(0, 10**6), 10**6) * M for _ in range(3))
    for _ in range(80000):
        b = 1 + F(rng.randint(0, 200000), 1000)
        yield sorted([b, b * rng.choice(RATS) + F(rng.randint(-3000, 3000), 1000), b * rng.choice(RATS) + F(rng.randint(-3000, 3000), 1000)])
for r in gen():
    if len(set(r)) < 3 or r[0] <= 1: continue
    s, t = chain([F(1)] + r); cnt += 1
    G = 5 * t; L = len(s)
    lb = min(L, 30) // 5 * 5
    bylen[lb] = max(bylen[lb], G)
    if s:
        mx = max(k for _, k in s); key = mx if mx <= 10 else (20 if mx <= 20 else (50 if mx <= 50 else 999))
        bymaxlap[key] = max(bymaxlap[key], G)
print('arrangements', cnt)
print('largest nearest reading by chain length (bucket start, 30 = 30+):', {k: round(float(v), 4) for k, v in sorted(bylen.items())})
print('largest nearest reading by the largest lap used (<=10 exact; 20, 50, 999 = buckets):', {k: round(float(v), 4) for k, v in sorted(bymaxlap.items())})
