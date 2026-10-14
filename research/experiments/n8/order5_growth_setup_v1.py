"""Order 5 growth bound: the exact multiplicative form of the walk, and the numbers it has to beat.

Exact relations (every step, any n; here n = 5). Write the setter of step j as x_j, its lap Q_j, its exit position
E_j = Q_j + 1/n (so t_{j+1} = E_j / x_j), and its entry position P_j = x_j t_j, with |P_j - Q_j| < 1/n. Then
    P_j = rho_j * E_{j-1},  rho_j = x_j / x_{j-1}   (ratios fixed by the speeds)
    R = n*m*t_N = n*E_N/s_N                          (s_N the last setter's reading)
    the true step factor is (Q_j + 1/n)/(Q_j - 1/n + delta_j),  delta_j = P_j - (Q_j - 1/n) in (0, 2/n).
Checks here, on both ends:
 (a) R = n*E_N/s_N exactly;
 (b) the cap R < n-1 holds iff the nearest runner is never in the way after the bound;
 (c) the true product against the lap-only bound prod F(Q_j) = prod (nQ+1)/(nQ-1): how much slack the depths carry;
 (d) the per-runner lap bound under a first exceedance: laps at steps before R reaches C are < (C*s + 1)/n - ... , i.e.
     Q < (C*s_x - 1)/n; record the largest lap actually used against that bound."""
import itertools, math, random, sys
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
n = 5; th = F(1, n); C = F(4)
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
def analyse(ds, c, slack, lapfrac):
    st, tend = walk(ds)
    if not st: c['no move'] += 1; return
    m = min(ds); R = n * m * tend
    idx, Q, tj = st[-1]
    if R != n * (Q + th) / (ds[idx] / m): c['identity R = n E/s FAILS'] += 1
    else: c['identity R = n E/s holds'] += 1
    near_inway = any(cdist(m * t) < th for _, _, t in st[1:]) or cdist(m * tend) < th
    c[('cap holds' if R < C else 'cap fails') + (', nearest in the way' if near_inway else ', nearest never in the way')] += 1
    true_prod = R
    lap_prod = math.prod([F(n * k + 1, n * k - 1) for _, k, _ in st], start=F(1))
    slack.append(float(lap_prod / true_prod))
    for i2, k, t in st:
        s = ds[i2] / m
        lapfrac.append(float(F(n * k + 1) / s))       # = R at that step; must stay < C before a first exceedance
def job_int(v):
    c = Counter(); sl = []; lf = []
    for i in range(n):
        ds = [F(abs(x - v[i])) for x in v if x != v[i]]
        analyse(ds, c, sl, lf)
    return c, sl, lf
RATS = [F(1), F(4, 3), F(3, 2), F(5, 3), F(2), F(5, 2), F(3), F(7, 4), F(5, 4)]
def job_res(seed):
    rng = random.Random(seed); c = Counter(); sl = []; lf = []
    for _ in range(150):
        b = F(rng.randint(20, 800)) + F(rng.randint(0, 999), 1000)
        r = sorted({F(1), b} | {max(F(1), b * rng.choice(RATS) + F(rng.randint(-3000, 3000), 1000)) for _ in range(2)})
        if len(r) == 4: analyse(r, c, sl, lf)
    return c, sl, lf
if __name__ == '__main__':
    for name, jobs, fn in (('integer [1,26]', list(itertools.combinations(range(1, 27), n)), job_int),
                           ('resonant', list(range(16)), job_res)):
        tot = Counter(); SL = []; LF = []
        with Pool() as pool:
            for c, sl, lf in pool.imap_unordered(fn, jobs, chunksize=50):
                tot.update(c); SL += sl; LF += lf
        SL.sort(); LF.sort()
        print(f'{name}: {dict(tot)}')
        if SL: print(f'   lap-only product / true R: median {SL[len(SL)//2]:.3f}, p99 {SL[int(len(SL)*0.99)]:.3f}, max {SL[-1]:.3f}')
        if LF: print(f'   R at each step: median {LF[len(LF)//2]:.3f}, p99 {LF[int(len(LF)*0.99)]:.3f}, max {LF[-1]:.4f}')
        sys.stdout.flush()
