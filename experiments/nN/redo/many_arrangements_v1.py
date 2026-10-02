"""E273/E274 (2026-10-02): many arrangements through the cascade.  Design: log E273.
Subject = the slowest runner; readings are positive integers (exact); cascade from the bound; landing lap K (8 h t* = 8K+1,
h the last setter, K = 0 at the bound) and R* = 8 d_min t*.  Checks: lonely at t* (exact); for small cells A.9's least opening."""
import random, sys, itertools
from fractions import Fraction as F
from math import floor
from multiprocessing import Pool
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade(T, cap=20000):
    t = F(1, 8 * min(T)); moves = 0; last = None
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t, moves, last
        best = None
        for d in way:
            k = floor(d * t - E8) + 1
            c = (F(k) + E8) / d
            if best is None or c > best[0]: best = (c, d, k)
        t, last = best[0], (best[1], best[2]); moves += 1
        if moves > cap: raise RuntimeError('cap')
def lonely(T, t): return all(nd(d * t) >= E8 for d in T)
def least_opening(T, tstar):
    best = None
    for h in T:
        K = 0
        while (F(8 * K + 1, 8 * h)) <= tstar:
            t = F(8 * K + 1, 8 * h)
            if lonely(T, t) and (best is None or t < best): best = t
            K += 1
    return best
G = 10**6
def gen(fam, par, rnd):
    if fam == 'F1': return sorted(rnd.sample(range(1, 7 * 10**6), 7))
    if fam == 'F2':
        rho = par; return [i * G + rnd.randint(-int(rho * G), int(rho * G)) for i in range(1, 8)]
    if fam == 'F3':
        W, rho = par; r = list(range(1, 8)); rnd.shuffle(r)
        return sorted((r[i] + 8 * rnd.randint(0, W)) * G + rnd.randint(-int(rho * G), int(rho * G)) for i in range(7))
    if fam == 'F4':
        j, rho, f = par; dev = lambda: rnd.randint(-int(rho * G), int(rho * G))
        cl = [i * G + dev() for i in range(1, j + 1)]
        out = [(f * rnd.randint(1, 9) + rnd.randrange(8)) * G + dev() for _ in range(7 - j)]
        return sorted(cl + out)
    if fam == 'F5':
        comp, f = par; res = []; scale = G
        for s in comp:
            base = rnd.randint(0, 5) * scale * 8 if res else 0
            res += [base + i * scale + rnd.randint(-int(0.1 * scale), int(0.1 * scale)) for i in range(1, s + 1)]
            scale *= f
        return sorted(res)
    if fam == 'F6':
        z, rho = par; dev = lambda: rnd.randint(-int(rho * G), int(rho * G))
        mult = [8 * rnd.randint(1, 50) * G + dev() for _ in range(z)]
        rest = [(rnd.randint(0, 50) * 8 + rnd.randint(1, 7)) * G + dev() for _ in range(7 - z)]
        return sorted(mult + rest)
def cell(args):
    fam, par, n, seed, check = args
    rnd = random.Random(seed); rows = []; bad = 0; badA9 = 0
    for _ in range(n):
        T = gen(fam, par, rnd)
        if len(set(T)) < 7 or min(T) <= 0: continue
        t, mv, last = cascade(T)
        if not lonely(T, t): bad += 1
        K = 0 if last is None else last[1]
        if check and sum(int(h * t) for h in T) < 200000:
            lo = least_opening(T, t)
            if lo != t and not (lo is None and last is None): badA9 += 1
        rows.append((K, mv, float(8 * min(T) * t), tuple(T)))
    return fam, par, rows, bad, badA9
CELLS = [('F1', None)] + [('F2', r) for r in (0.01, 0.1, 0.3, 0.45)] + [('F3', (W, r)) for W in (10, 10**3, 10**6) for r in (0, 0.01, 0.1, 0.3, 0.45)] \
    + [('F4', (j, r, f)) for j in (1, 3, 5) for r in (0, 0.1, 0.3) for f in (10, 10**3, 10**6, 10**9)] \
    + [('F5', (c, f)) for c in ((3, 4), (2, 2, 3), (1, 3, 3)) for f in (10, 10**3, 10**6)] + [('F6', (z, r)) for z in (2, 3, 4) for r in (0, 0.1, 0.3)]
if __name__ == '__main__':
    out = open('many_arrangements_v1.out', 'w'); out.write(__doc__ + "\n")
    def w(s): out.write(s + "\n"); out.flush()
    jobs = [(f, p, 300, 7000 + i, i % 4 == 0) for i, (f, p) in enumerate(CELLS)]
    with Pool(10) as pool: res = pool.map(cell, jobs)
    tb = ta = 0
    for fam, par, rows, bad, badA9 in res:
        tb += bad; ta += badA9
        if not rows: w("%s %s: no valid arrangements" % (fam, par)); continue
        mK = max(r[0] for r in rows); mM = max(r[1] for r in rows); mR = max(r[2] for r in rows)
        w("%s %-22s n=%3d  max K %-6d max moves %-3d max R* %-10.3f  not lonely %d  A.9 mismatches %d" % (fam, par, len(rows), mK, mM, mR, bad, badA9))
    w("\nCHECKS: not lonely at the landing: %d; A.9 least-opening mismatches: %d" % (tb, ta))
    allrows = [(r, fam, par) for fam, par, rows, _, _ in res for r in rows]
    w("\nthe 12 arrangements with the largest K:")
    for r, fam, par in sorted(allrows, key=lambda x: -x[0][0])[:12]: w("  K %d moves %d R* %.3f  %s %s  %s" % (r[0], r[1], r[2], fam, par, r[3]))
    w("the 12 with the most moves:")
    for r, fam, par in sorted(allrows, key=lambda x: -x[0][1])[:12]: w("  moves %d K %d R* %.3f  %s %s  %s" % (r[1], r[0], r[2], fam, par, r[3]))
    out.close(); print(open('many_arrangements_v1.out').read()[len(__doc__):])
