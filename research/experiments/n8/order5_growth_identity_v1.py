"""The growth identity. For a cascade with setters x_1..x_N (readings s_j = x_j/m), laps Q_j, entry P_j = x_j t_j and
depth delta_j = P_j - (Q_j - 1/n) in (0, 2/n):

        E_j = Q_j + 1/n = rho_j E_{j-1} + (2/n - delta_j),   rho_j = x_j/x_{j-1}
   =>   R  = R_1 + sum_{j>=2} (2 - n*delta_j)/s_j            (R_1 = the R after the first move)

Checked exactly (Fractions) at both ends, together with the terms' sizes: R_1, the number of moves, sum of (2 - n delta)/s,
and the largest single term."""
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
def analyse(ds, c, terms, r1s):
    st, tend = walk(ds)
    if not st: return
    m = min(ds); R = n * m * tend
    R1 = None; tot = F(0)
    for j, (idx, Q, tj) in enumerate(st):
        s = ds[idx] / m; P = ds[idx] * tj; delta = P - (Q - th)
        if not (0 < delta < 2 * th): c['delta out of range'] += 1
        if j == 0:
            R1 = n * (Q + th) / s
        else:
            term = (2 - n * delta) / s
            tot += term; terms.append(float(term))
    r1s.append(float(R1))
    c['identity holds' if R == R1 + tot else 'identity FAILS'] += 1
def job_int(v):
    c = Counter(); te = []; r1 = []
    for i in range(n):
        ds = [F(abs(x - v[i])) for x in v if x != v[i]]
        analyse(ds, c, te, r1)
    return c, te, r1
RATS = [F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3), F(7, 4), F(5, 4)]
def job_res(seed):
    rng = random.Random(seed); c = Counter(); te = []; r1 = []
    for _ in range(150):
        b = F(rng.randint(20, 800)) + F(rng.randint(0, 999), 1000)
        r = sorted({F(1), b} | {max(F(1), b * rng.choice(RATS) + F(rng.randint(-3000, 3000), 1000)) for _ in range(2)})
        if len(r) == 4: analyse(r, c, te, r1)
    return c, te, r1
if __name__ == '__main__':
    for name, jobs, fn in (('integer [1,26]', list(itertools.combinations(range(1, 27), n)), job_int),
                           ('resonant', list(range(16)), job_res)):
        tot = Counter(); TE = []; R1 = []
        with Pool() as pool:
            for c, te, r1 in pool.imap_unordered(fn, jobs, chunksize=50):
                tot.update(c); TE += te; R1 += r1
        TE.sort(); R1.sort()
        print(f'{name}: {dict(tot)}')
        if R1: print(f'   R_1 (after the first move): median {R1[len(R1)//2]:.4f}, max {R1[-1]:.4f}')
        if TE: print(f'   terms (2 - n*delta)/s: {len(TE)} of them; median {TE[len(TE)//2]:.4f}, p99 {TE[int(len(TE)*0.99)]:.4f}, max {TE[-1]:.4f}, negative: {sum(1 for x in TE if x < 0)}')
        sys.stdout.flush()
