"""Why the lap-decrease measure fails. Hypothesis: a nested return needs the inner runner to visit two of its lap zones inside
one stretch of the parent's, and its zones are spaced 1/d apart in time, so the inner runner must be at least about as fast as
the parent; at a common instant lap = difference x time, so its laps are at least the parent's.

For every nested return (integer range, and the resonant generator): record d_inner/d_parent, the parent's lap Q, the inner
laps, the stretch length in time, and 1/d_inner, and check
  (a) d_inner >= d_parent ?
  (b) stretch length >= 2/d_inner (room for two openings) ?
  (c) inner lap >= parent lap ?"""
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
def scan(ds, c, ratios):
    st, tend = walk(ds)
    times = [t for _, _, t in st] + [tend]
    pos = {}
    for j, (idx, k, _) in enumerate(st):
        if idx in pos:
            j0, Q = pos[idx]; inner = st[j0 + 1:j]; seen = {}
            span = times[j] - times[j0 + 1]
            for jj, (idx2, k2, _) in enumerate(inner):
                if idx2 in seen:
                    c['nested'] += 1
                    r = ds[idx2] / ds[idx]
                    ratios.append(float(r))
                    c['inner at least as fast' if ds[idx2] >= ds[idx] else 'inner slower'] += 1
                    c['inner lap >= parent lap' if max(seen[idx2], k2) >= Q else 'inner lap < parent lap'] += 1
                    c['stretch fits two inner openings' if span >= 2 / ds[idx2] else 'stretch shorter than two inner openings'] += 1
                seen[idx2] = k2
        pos[idx] = (j, k)
def job_int(v):
    c = Counter(); ratios = []
    for i in range(n):
        ds = [F(abs(x - v[i])) for x in v if x != v[i]]
        scan(ds, c, ratios)
    return c, ratios
RATS = [F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3), F(7, 4), F(5, 4)]
def job_res(seed):
    rng = random.Random(seed); c = Counter(); ratios = []
    for _ in range(120):
        b = F(rng.randint(20, 800)) + F(rng.randint(0, 999), 1000)
        r = sorted({F(1), b} | {max(F(1), b * rng.choice(RATS) + F(rng.randint(-3000, 3000), 1000)) for _ in range(2)})
        if len(r) == 4: scan(r, c, ratios)
    return c, ratios
if __name__ == '__main__':
    for name, jobs, fn in (('integer [1,24]', list(itertools.combinations(range(1, 25), n)), job_int),
                           ('resonant', list(range(16)), job_res)):
        tot = Counter(); RA = []
        with Pool() as pool:
            for c, ra in pool.imap_unordered(fn, jobs, chunksize=50):
                tot.update(c); RA += ra
        RA.sort()
        print(f'{name}: {dict(tot)}')
        if RA:
            print(f'   d_inner/d_parent: min {RA[0]:.3f}, median {RA[len(RA)//2]:.3f}, max {RA[-1]:.3f}; below 1 in {sum(1 for x in RA if x < 1)} of {len(RA)}')
        sys.stdout.flush()
