"""E662. E558's method on the two-block template. Speeds 0..p-1 (block L, step 1; any positive common speed may be added)
and A + i b (block R, i < 8-p) with A = (p-1) + G; subject k = p-1 (the end of L at the gap), so its nearest runner is
across the gap at distance G. t0 = 1/(8G) = N + tau0. Own readings are the whole numbers 1..p-1, whose phases at
t0 + D depend on tau0 only; other readings G + i b, whose phases carry frac(b t0) as well. For b = P/Q that phase is
fixed by tau0 and r = N mod Q. Test (as E558): Delta = landing - t0 for N = 30Q + r, 120Q + r, 480Q + r against
N = 100000Q + r, tau0 on a 1/48 grid, every r. Cascade unchanged (catalogue_by_outcome_v1.py); oracle check C1 for
N <= 480Q + r. Exact Fractions."""
import math
from fractions import Fraction as F
E = F(1, 8)
def dist(x):
    f = x - math.floor(x); return min(f, 1 - f)
def cascade(r):
    t = F(1, 8 * r[0]); moves = 0
    while True:
        way = [(i, d) for i, d in enumerate(r) if dist(d * t) < E]
        if not way: return t, moves
        best = None
        for i, d in way:
            M = round(d * t); nt = (F(M) + E) / d
            if best is None or nt > best[0]: best = (nt, i, M)
        t = best[0]; moves += 1
def first_lonely(r, upto):
    lo = F(1, 8 * r[0]); c = {lo}
    for d in r:
        for M in range(math.floor(d * lo), math.floor(d * upto) + 1): c.add((F(M) + E) / d)
    for t in sorted(c):
        if lo <= t <= upto and all(dist(d * t) >= E for d in r): return t
def readings(p, b, G):
    return sorted([F(j) for j in range(1, p)] + [G + i * b for i in range(8 - p)])
def shift(p, b, N, tau0, check):
    G = 1 / (8 * (N + tau0)); r = readings(p, b, G)
    t, mv = cascade(r)
    if check: assert first_lonely(r, t) == t
    return t - (N + tau0), mv
for p, b in [(2, F(3, 2)), (4, F(3, 2)), (4, F(5, 3)), (6, F(2, 3)), (3, F(7, 4)), (5, F(4, 3))]:
    Q = b.denominator
    worst = F(0); vals = set(); n = 0
    for r_ in range(Q):
        for j in range(48):
            tau0 = F(j, 48)
            lim, _ = shift(p, b, 100000 * Q + r_, tau0, False)
            vals.add((r_, lim))
            for m in (30, 120, 480):
                d, _ = shift(p, b, m * Q + r_, tau0, True); n += 1
                worst = max(worst, abs(d - lim))
    print("p=%d b=%s (Q=%d): %d (tau0, r) cells, %d finite-N cascades (C1 checked), distinct limit Delta: %d, max |Delta(N) - Delta(limit)| = %.6f" %
          (p, b, Q, 48 * Q, n, len({v for _, v in vals}), float(worst)))
