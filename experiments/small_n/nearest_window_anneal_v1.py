"""Adversarial search, n = 5, 6, 7, 8: largest final nearest-runner reading n*m*T over subjects with n-1 differences
(ratios to the nearest >= 1).  Reports whether the nearest runner is ever in the way at an iterate (leaves [1, n-1])."""
from fractions import Fraction as F
import math, random, sys
from multiprocessing import Pool
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
def chain(ds, n):
    th = F(1, n); t = th / ds[0]; near = False; moves = 0
    while True:
        best = t; who = None
        for i, d in enumerate(ds):
            if cd(d * t) < th:
                if i == 0: near = True
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, i
        if who is None: return n * t, near, moves
        t = best; moves += 1
def score(r, n):
    return chain([F(1)] + sorted(r), n)
def anneal(args):
    n, seed, iters = args
    rng = random.Random(seed)
    k = n - 2
    scale = rng.choice([3, 10, 30])
    cur = [1 + F(rng.randint(0, 1000 * scale), 1000) for _ in range(k)]
    cs, cn, _ = score(cur, n); best = (cs, cn, list(cur))
    for it in range(iters):
        T = 0.3 * (1 - it / iters) + 0.002
        step = F(rng.choice([1, 10, 100, 1000]), 1000)
        new = [max(F(1), x + step * F(rng.randint(-100, 100), 100)) if rng.random() < 0.6 else x for x in cur]
        ns, nn, _ = score(new, n)
        if ns >= cs or rng.random() < math.exp(float(ns - cs) / T):
            cur, cs, cn = new, ns, nn
            if cs > best[0]: best = (cs, cn, list(cur))
        if cn: best = max(best, (cs, cn, list(cur)), key=lambda b: (b[1], b[0]))
    return n, best
if __name__ == '__main__':
    jobs = [(n, s, 2500 if n <= 6 else 1500) for n in (5, 6, 7, 8) for s in range(16)]
    with Pool() as p:
        res = p.map(anneal, jobs)
    for n in (5, 6, 7, 8):
        rs = [b for m, b in res if m == n]
        top = max(rs, key=lambda b: b[0]); anyin = [b for b in rs if b[1]]
        print(f'n={n}: largest nearest reading {float(top[0]):.4f} (edge {n-1}) at ratios {[round(float(x), 4) for x in sorted(top[2])]}; '
              f'runs finding the nearest runner in the way: {len(anyin)} of {len(rs)}')
        if anyin:
            b = max(anyin, key=lambda b: b[0]); print(f'     e.g. reading {float(b[0]):.4f} at {[round(float(x), 4) for x in sorted(b[2])]}')
