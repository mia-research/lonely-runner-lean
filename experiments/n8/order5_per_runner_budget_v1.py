"""Per-runner budget. By the growth identity R = R_1 + sum_j (2 - n*delta_j)/s_j, each runner x contributes
    B_x = sum over x's settings of (2 - n*delta)/s_x.
If B_x <= c for every runner, then at order 5 with four differences R <= 3/2 + 4c, and the cap R < 4 follows from c < 5/8.
Measured exactly at both ends: the distribution of B_x, the worst B_x, the number of settings behind it, and the resulting
bound 3/2 + (k-1)*max B_x against the observed max R."""
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
def analyse(ds, out, Rs):
    st, tend = walk(ds)
    if not st: return
    m = min(ds); B = {}; cnt = Counter()
    for j, (idx, Q, tj) in enumerate(st):
        if j == 0: continue
        s = ds[idx] / m; delta = ds[idx] * tj - (Q - th)
        B[idx] = B.get(idx, F(0)) + (2 - n * delta) / s
        cnt[idx] += 1
    Rs.append(float(n * m * tend))
    for idx, b in B.items(): out.append((float(b), cnt[idx]))
def job_int(v):
    o = []; R = []
    for i in range(n):
        ds = [F(abs(x - v[i])) for x in v if x != v[i]]
        analyse(ds, o, R)
    return o, R
RATS = [F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3), F(7, 4), F(5, 4)]
def job_res(seed):
    rng = random.Random(seed); o = []; R = []
    for _ in range(150):
        b = F(rng.randint(20, 800)) + F(rng.randint(0, 999), 1000)
        r = sorted({F(1), b} | {max(F(1), b * rng.choice(RATS) + F(rng.randint(-3000, 3000), 1000)) for _ in range(2)})
        if len(r) == 4: analyse(r, o, R)
    return o, R
if __name__ == '__main__':
    for name, jobs, fn in (('integer [1,26]', list(itertools.combinations(range(1, 27), n)), job_int),
                           ('resonant', list(range(16)), job_res)):
        O = []; RR = []
        with Pool() as pool:
            for o, R in pool.imap_unordered(fn, jobs, chunksize=50):
                O += o; RR += R
        O.sort(); RR.sort()
        bs = [b for b, _ in O]
        print(f'{name}: {len(O)} runner-contributions, {len(RR)} walks')
        print(f'   B_x: median {bs[len(bs)//2]:.4f}, p99 {bs[int(len(bs)*0.99)]:.4f}, max {bs[-1]:.4f}')
        worst = max(O); print(f'   worst B_x {worst[0]:.4f} from {worst[1]} settings')
        print(f'   bound 3/2 + 3*max(B_x) = {1.5 + 3*bs[-1]:.4f}; observed max R = {RR[-1]:.4f}')
        sys.stdout.flush()
