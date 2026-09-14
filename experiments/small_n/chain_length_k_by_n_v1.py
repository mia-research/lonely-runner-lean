"""Longest moment-iteration chain for k differences at threshold 1/n (k <= n-1): random, near-rational, and annealing on
chain length.  Also the largest final nearest reading and whether the nearest runner is ever in the way."""
from fractions import Fraction as F
import math, random
from multiprocessing import Pool
def cd(x):
    f = x - math.floor(x); return min(f, 1 - f)
def chain(ds, n):
    th = F(1, n); t = th / ds[0]; L = 0; near = False
    while True:
        best = t; who = None
        for i, d in enumerate(ds):
            if cd(d * t) < th:
                if i == 0: near = True
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, i
        if who is None: return L, n * t, near
        t = best; L += 1
        if L > 2000: return L, n * t, near
RATS = [F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3), F(4), F(5)]
def job(args):
    k, n, seed = args
    rng = random.Random(seed)
    bestL = 0; bestR = F(0); near = 0; ex = None
    def rec(r):
        nonlocal bestL, bestR, near, ex
        L, R, nr = chain([F(1)] + sorted(r), n)
        if L > bestL: bestL, ex = L, sorted(r)
        bestR = max(bestR, R); near += nr
        return L
    for _ in range(3000):
        if rng.random() < 0.5:
            M = rng.choice([3, 10, 50, 300])
            r = [1 + F(rng.randint(0, 10**5), 10**5) * M for _ in range(k - 1)]
        else:
            b = 1 + F(rng.randint(0, 50000), 1000)
            r = [b] + [b * rng.choice(RATS) + F(rng.randint(-2000, 2000), 1000) for _ in range(k - 2)]
        r = [max(F(1), x) for x in r]
        if len(set(r)) < k - 1: continue
        rec(r)
    # anneal on length
    cur = ex if ex else [1 + F(rng.randint(0, 5000), 1000) for _ in range(k - 1)]
    cl = chain([F(1)] + sorted(cur), n)[0]
    for it in range(2500):
        step = F(rng.choice([1, 10, 100, 1000]), 1000)
        new = [max(F(1), x + step * F(rng.randint(-100, 100), 100)) for x in cur]
        if len(set(new)) < k - 1: continue
        nl = rec(new)
        if nl >= cl or rng.random() < 0.02: cur, cl = new, nl
    return k, n, bestL, bestR, near, ex
if __name__ == '__main__':
    jobs = [(k, n, s) for k in (2, 3, 4, 5) for n in range(k + 1, 3 * k + 3) for s in range(6)]
    with Pool() as p: res = p.map(job, jobs)
    agg = {}
    for k, n, L, R, near, ex in res:
        a = agg.setdefault((k, n), [0, F(0), 0, None])
        if L > a[0]: a[0], a[3] = L, ex
        a[1] = max(a[1], R); a[2] += near
    for k in (2, 3, 4, 5):
        row = [f'n={n}: L={agg[(k,n)][0]} R={float(agg[(k,n)][1]):.2f}{"*" if agg[(k,n)][2] else ""}' for n in range(k + 1, 3 * k + 3)]
        print(f'k={k} differences: ' + ' | '.join(row))
    print('(L = longest chain found; R = largest nearest reading; * = nearest runner in the way somewhere)')
