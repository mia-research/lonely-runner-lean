"""How much of the worst case the growth actually uses, order 5, both ends.
Per walk:  A = R - R_1 = sum of terms;  W = sum over settings of 2/s (the worst-case charge);  ratio A/W.
Per return: the cost in units of (n-2)/s_x  (the proved minimum is 1).
The diagonal wall: charging every setting 2/s and every return the minimum (n-2)/s gives A <= 2*Sigma(1/s) + 2k*A/(n-2),
which closes only if 2k < n-2. At order 5, k=4: 2k/(n-2) = 8/3. So the average discount must beat 8/3 ~ 2.67 for the
accounting to close; this measures what it actually is."""
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
    if len(st) < 2: return
    m = min(ds); A = F(0); W = F(0); seen = {}
    for j, (idx, Q, tj) in enumerate(st):
        s = ds[idx] / m; delta = ds[idx] * tj - (Q - th); R_here = n * m * tj
        if j > 0:
            A += (2 - n * delta) / s; W += 2 / s
        if idx in seen:
            acc['cost'].append(float((R_here - seen[idx]) * s / (n - 2)))
        seen[idx] = R_here
    if W > 0: acc['ratio'].append(float(W / A))
def job_int(v):
    acc = {'ratio': [], 'cost': []}
    for i in range(n):
        ds = [F(abs(x - v[i])) for x in v if x != v[i]]
        analyse(ds, acc)
    return acc
RATS = [F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3), F(7, 4), F(5, 4)]
def job_res(seed):
    rng = random.Random(seed); acc = {'ratio': [], 'cost': []}
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
        A = {'ratio': [], 'cost': []}
        with Pool() as pool:
            for acc in pool.imap_unordered(fn, jobs, chunksize=50): merge(A, acc)
        r = sorted(A['ratio']); c = sorted(A['cost'])
        if r: print(f'{name}: {len(r)} walks with 2+ moves; worst-case charge / actual growth: min {r[0]:.3f}, median {r[len(r)//2]:.3f}, p99 {r[int(len(r)*0.99)]:.3f}, max {r[-1]:.3f}  (needs to beat 8/3 = 2.667)')
        if c: print(f'   return cost in units of (n-2)/s: min {c[0]:.3f}, median {c[len(c)//2]:.3f}, max {c[-1]:.3f}')
        sys.stdout.flush()
