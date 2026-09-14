"""n=5 large-lap regime: largest final nearest reading when the slowest other runner has ratio >= M
(annealing + near-rational seeds), M in {2, 5, 20, 100, 1000}."""
from fractions import Fraction as F
import math, random, sys
from multiprocessing import Pool
th = F(1, 5)
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
def reading(r):
    ds = [F(1)] + sorted(r); t = th; L = 0
    while True:
        best = t; who = None
        for d in ds:
            if cd(d * t) < th:
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, d
        if who is None: return 5 * t, L
        t = best; L += 1
        if L > 5000: return 5 * t, L
RATS = [F(1), F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3), F(4)]
def job(args):
    M, seed = args
    rng = random.Random(seed)
    def clamp(r): return [max(F(M), x) for x in r]
    best = (F(0), None, 0)
    def rec(r):
        nonlocal best
        r = clamp(r)
        if len(set(r)) < 3: return F(0)
        R, L = reading(r)
        if R > best[0]: best = (R, sorted(r), L)
        return R
    # seeds: near-rational around M
    starts = []
    for _ in range(40):
        b = F(M) + F(rng.randint(0, 10**6), 10**6) * M
        starts.append([b, b * rng.choice(RATS) + F(rng.randint(-1000, 1000), 10**4), b * rng.choice(RATS) + F(rng.randint(-1000, 1000), 10**4)])
    for st in starts:
        cur = clamp(st); cs = rec(cur)
        for it in range(600):
            scale = [F(1, 10), F(1, 1000), F(1, 100000)][it * 3 // 600] * M
            new = [x + scale * F(rng.randint(-100, 100), 100) for x in cur]
            ns = rec(new)
            if ns >= cs: cur, cs = clamp(new), ns
    return M, best
if __name__ == '__main__':
    jobs = [(M, s) for M in (2, 5, 20, 100, 1000) for s in range(8)]
    with Pool() as p: res = p.map(job, jobs)
    for M in (2, 5, 20, 100, 1000):
        b = max((r for m, r in res if m == M), key=lambda r: r[0])
        print(f'slowest ratio >= {M}: largest nearest reading {float(b[0]):.4f} (chain {b[2]} moves) at ratios {[float(x) for x in b[1]]}')
