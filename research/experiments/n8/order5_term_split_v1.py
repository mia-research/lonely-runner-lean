"""Where the growth actually goes. Using R = R_1 + sum_j (2 - n*delta_j)/s_j at order 5:
 - split the total addition into the runners' FIRST settings and their REPEAT settings;
 - record, per walk, the total addition, and the largest addition seen;
 - record term size against the setter's reading s and against its setting index (1st, 2nd, 3rd, ...);
 - record the number of settings a runner of reading s makes, against the cap bound floor((4s-1)/5).
Exact."""
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
    m = min(ds); seen = Counter(); first_tot = F(0); rep_tot = F(0)
    for j, (idx, Q, tj) in enumerate(st):
        s = ds[idx] / m; delta = ds[idx] * tj - (Q - th); term = (2 - n * delta) / s
        seen[idx] += 1
        if j == 0: continue
        if seen[idx] == 1: first_tot += term
        else: rep_tot += term
        acc['by_index'].append((min(seen[idx], 4), float(term)))
        acc['by_s'].append((float(s), float(term)))
    acc['totals'].append((float(first_tot), float(rep_tot), float(n * m * tend)))
    for idx, c in seen.items():
        s = ds[idx] / m; acc['settings'].append((float(s), c, math.floor((4 * s - 1) / 5)))
def job_int(v):
    acc = {'by_index': [], 'by_s': [], 'totals': [], 'settings': []}
    for i in range(n):
        ds = [F(abs(x - v[i])) for x in v if x != v[i]]
        analyse(ds, acc)
    return acc
RATS = [F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3), F(7, 4), F(5, 4)]
def job_res(seed):
    rng = random.Random(seed); acc = {'by_index': [], 'by_s': [], 'totals': [], 'settings': []}
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
        A = {'by_index': [], 'by_s': [], 'totals': [], 'settings': []}
        with Pool() as pool:
            for acc in pool.imap_unordered(fn, jobs, chunksize=50): merge(A, acc)
        T = A['totals']; tot_add = sorted(f + r for f, r, _ in T)
        print(f'{name}: {len(T)} walks with a move')
        print(f'   total addition R - R_1: median {tot_add[len(tot_add)//2]:.4f}, p99 {tot_add[int(len(tot_add)*0.99)]:.4f}, max {tot_add[-1]:.4f}')
        fs = sorted(f for f, r, _ in T); rs = sorted(r for f, r, _ in T)
        print(f'   from first settings: median {fs[len(fs)//2]:.4f}, max {fs[-1]:.4f}; from repeats: median {rs[len(rs)//2]:.4f}, max {rs[-1]:.4f}')
        for i in (1, 2, 3, 4):
            v = sorted(t for k, t in A['by_index'] if k == i)
            if v: print(f'   term at setting #{i}{"+" if i == 4 else ""}: {len(v)} terms, median {v[len(v)//2]:.4f}, max {v[-1]:.4f}')
        st = A['settings']; viol = [x for x in st if x[1] > max(x[2], 1)]
        print(f'   settings by a runner of reading s: max {max(c for _, c, _ in st)}; exceeding floor((4s-1)/5) (at least 1): {len(viol)} of {len(st)}')
        sys.stdout.flush()
