"""Order 5, near-rational speed ratios (the generator of experiments/small_n/n5_cycles_v1.py): for chains of 25+ moves,
how many times each runner sets, its largest setting lap, R, the setter-lap product prod F(Q_j), and the bound
prod_x g(L_x) with L_x = floor(s_x R/n + 1/n). Exact rationals."""
from fractions import Fraction as F
import math, random
n = 5; th = F(1, n)
def cdist(x):
    f = x - math.floor(x); return min(f, 1 - f)
def chain(ds):
    t = th / ds[0]; steps = []
    while True:
        best = t; who = None
        for i, d in enumerate(ds):
            if cdist(d * t) < th:
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, (i, k)
        if who is None: return t, steps
        steps.append(who); t = best
rng = random.Random(8)
RATS = [F(1), F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3)]
found = []
for _ in range(120000):
    b = F(rng.randint(20, 1000)) + F(rng.randint(0, 999), 1000)
    r = sorted([b, b * rng.choice(RATS) + F(rng.randint(-3000, 3000), 1000), b * rng.choice(RATS) + F(rng.randint(-3000, 3000), 1000)])
    if len(set(r)) < 3 or r[0] <= 1: continue
    ds = [F(1)] + r
    t, s = chain(ds)
    if len(s) >= 25: found.append((len(s), ds, t, s))
found.sort(key=lambda x: -x[0])
print('chains with >= 25 moves:', len(found))
for L, ds, t, s in found[:6]:
    R = n * t
    cnt = [sum(1 for i, _ in s if i == j) for j in range(4)]
    mx = [max([q for i, q in s if i == j], default=0) for j in range(4)]
    P = math.prod((F(n * q + 1, n * q - 1) for _, q in s), start=F(1))
    B = math.prod((math.prod((F(n * r + 1, n * r - 1) for r in range(1, math.floor(x * R / n + th) + 1)), start=F(1)) for x in ds), start=F(1))
    print(f'moves {L:4d}  R {float(R):.4f}  settings per runner (a,b,c,d) {cnt}  largest lap {mx}  prod F {float(P):.3e}  prod g {float(B):.3e}')
