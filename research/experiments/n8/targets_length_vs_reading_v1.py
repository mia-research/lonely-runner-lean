"""Order 5: longest cascade (moves) by the largest reading s_max, exact rationals. Generators: uniform readings, and
near-rational ratios (b, b·r + ε) as in n5_cycles_v1.py, with b scaled into each band. Question: does chain length stay
bounded when readings are bounded?"""
from fractions import Fraction as F
import math, random
from multiprocessing import Pool
n = 5; th = F(1, n)
def cdist(x):
    f = x - math.floor(x); return min(f, 1 - f)
def chain_len(ds, cap=5000):
    t = th / ds[0]; L = 0
    while L < cap:
        best = t
        for d in ds:
            if cdist(d * t) < th:
                o = (math.ceil(d * t - th) + th) / d
                if o > best: best = o
        if best == t: return L, n * t
        t = best; L += 1
    return L, n * t
RATS = [F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3), F(7, 4), F(5, 4)]
BANDS = [(1, 3), (3, 6), (6, 10), (10, 20), (20, 50), (50, 200), (200, 1000)]
def job(args):
    band, seed = args; lo, hi = band; rng = random.Random(seed); best = (0, None, None)
    for it in range(4000):
        if it % 2:
            ds = sorted({F(1)} | {F(lo) + F(rng.randint(0, 10**6), 10**6) * (hi - lo) for _ in range(3)})
        else:
            b = F(lo) + F(rng.randint(0, 10**6), 10**6) * (hi - lo)
            eps = F(rng.randint(-10**4, 10**4), 10**6) * b
            ds = sorted({F(1), b} | {max(F(1), min(F(hi), b * rng.choice(RATS) + eps * rng.choice([1, -1, F(1, 3)]))) for _ in range(2)})
        if len(ds) != 4 or ds[-1] > hi: continue
        L, R = chain_len(ds)
        if L > best[0]: best = (L, float(R), [round(float(x), 4) for x in ds])
    return band, best
if __name__ == '__main__':
    tasks = [(b, s) for b in BANDS for s in range(8)]
    with Pool() as p: res = p.map(job, tasks)
    for b in BANDS:
        rows = [r for bb, r in res if bb == b]
        top = max(rows, key=lambda r: r[0])
        R = 'n/a' if top[1] is None else f'{top[1]:.4f}'
        print(f's_max in [{b[0]:4d},{b[1]:4d}]: longest chain {top[0]:5d} moves (R {R}) at readings {top[2]}')
