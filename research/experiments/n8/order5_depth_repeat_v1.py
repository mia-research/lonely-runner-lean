"""Depth at repeat settings, order 5, both ends. For every setting of a runner x beyond its first, record:
  - the depth delta at that setting (how far into its zone it was),
  - the growth dR since x's previous setting,
  - the check dR > (n-2)/s_x  (a return costs x a reading increase > n-2, so R must rise by more than (n-2)/s_x),
  - the number of intervening moves,
and per walk the ledger  sum over runners of (returns)/s_x < 1  (from the cap R < n-1 and R_1 >= 1).
Also the depth at first settings, for comparison. Exact."""
import itertools, math, random, sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
n = 5; th = F(1, n)
def cdist(x):
    f = x - math.floor(x); return min(f, 1 - f)
def walk(ds):
    t = th / min(ds); steps = []
    while True:
        best = t; who = None
        for idx, d in enumerate(ds):
            if cdist(d * t) < th:
                k = math.ceil(d * t - th); o = (k + th) / d
                if o > best: best, who = o, (idx, k, t)
        if who is None: return steps, t
        steps.append(who); t = best
def analyse(ds, acc):
    st, tend = walk(ds)
    if not st: return
    m = min(ds); seen = {}; rets = Counter()
    for j, (idx, Q, tj) in enumerate(st):
        s = ds[idx] / m; delta = ds[idx] * tj - (Q - th); R_here = n * m * tj
        if idx in seen:
            jprev, Rprev = seen[idx]
            dR = R_here - Rprev
            acc['repeat'].append((float(delta), float(dR), float(dR * s), j - jprev - 1))
            acc['cost_ok'].append(dR > F(n - 2) / s)
            rets[idx] += 1
        else:
            acc['first'].append(float(delta))
        seen[idx] = (j, R_here)
    acc['ledger'].append(float(sum(F(r) / (ds[i] / m) for i, r in rets.items())))
def job_int(v):
    acc = {'first': [], 'repeat': [], 'cost_ok': [], 'ledger': []}
    for i in range(n):
        ds = [F(abs(x - v[i])) for x in v if x != v[i]]
        analyse(ds, acc)
    return acc
RATS = [F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3), F(7, 4), F(5, 4)]
def job_res(seed):
    rng = random.Random(seed); acc = {'first': [], 'repeat': [], 'cost_ok': [], 'ledger': []}
    for _ in range(150):
        b = F(rng.randint(20, 800)) + F(rng.randint(0, 999), 1000)
        r = sorted({F(1), b} | {max(F(1), b * rng.choice(RATS) + F(rng.randint(-3000, 3000), 1000)) for _ in range(2)})
        if len(r) == 4: analyse(r, acc)
    return acc
def merge(a, b):
    for k in a: a[k] += b[k]
    return a
if __name__ == '__main__':
    for name, jobs, fn in (('integer [1,26]', list(itertools.combinations(range(1, 27), n)), job_int),
                           ('resonant', list(range(16)), job_res)):
        A = {'first': [], 'repeat': [], 'cost_ok': [], 'ledger': []}
        with Pool() as pool:
            for acc in pool.imap_unordered(fn, jobs, chunksize=50): merge(A, acc)
        f = sorted(A['first']); rp = A['repeat']; led = sorted(A['ledger'])
        print(f'{name}: {len(f)} first settings, {len(rp)} repeat settings')
        if f: print(f'   depth at a first setting: min {f[0]:.5f}, median {f[len(f)//2]:.4f}, max {f[-1]:.4f} (range is (0, 0.4))')
        if rp:
            d = sorted(x[0] for x in rp); g = sorted(x[1] for x in rp); rs = sorted(x[2] for x in rp); iv = Counter(x[3] for x in rp)
            print(f'   depth at a repeat setting: min {d[0]:.5f}, 1st pct {d[len(d)//100]:.5f}, median {d[len(d)//2]:.4f}, max {d[-1]:.4f}')
            print(f'   growth dR since the previous setting: min {g[0]:.5f}, median {g[len(g)//2]:.4f}')
            print(f'   x-reading increase s_x*dR (must exceed n-2 = 3): min {rs[0]:.4f}, median {rs[len(rs)//2]:.4f}')
            print(f'   cost check dR > (n-2)/s_x: {sum(A["cost_ok"])} of {len(A["cost_ok"])}')
            print(f'   intervening moves: {dict(sorted(iv.items()))}')
        if led: print(f'   ledger sum(returns/s_x): median {led[len(led)//2]:.4f}, max {led[-1]:.4f} (must stay below 1)')
        sys.stdout.flush()
