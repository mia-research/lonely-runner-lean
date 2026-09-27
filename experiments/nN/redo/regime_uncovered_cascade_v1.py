"""E156: the sets the regime covering misses, through the cascade: landing R* (units of m), flank rank and lap, the chain,
the laps at the landing, and the gaps (consecutive ratios); then the slow-block window at EVERY split and lap 0/1 to see
which split the landing sits in.  Exact."""
from fractions import Fraction as F
from math import floor
sys_path = __import__('sys').path; sys_path.insert(0, '../band_cert_v1'); from core import clear_set
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def chain(T):
    t = F(1, 8 * T[0]); mv = []
    while True:
        W = [d for d in T if nd(d * t) < E8]
        if not W: return t, mv
        ex = {d: (F(floor(d * t - E8) + 1) + E8) / d for d in W}
        t2 = max(ex.values()); a = max(W, key=lambda d: ex[d]); mv.append((T.index(a), floor(a * t2), round(float(8 * T[0] * t2), 4))); t = t2
SETS = [(1, 2, 3, 6, 7, 16, 20), (1, 2, 3, 6, 7, 16, 21), (1, 2, 3, 6, 7, 21, 24), (1, 2, 3, 7, 18, 23, 24), (1, 2, 3, 7, 19, 20, 24),
        (1, 2, 4, 6, 14, 15, 16), (1, 2, 4, 7, 8, 18, 23), (1, 3, 6, 21, 22, 23, 24), (1, 2, 3, 4, 6, 7, 32), (1, 2, 3, 6, 7, 24, 27),
        (1, 8, 13, 19, 35, 318, 748), (1, 4, 15, 96, 252, 537, 1885), (1, 2, 8, 28, 200, 343, 1141), (24, 25, 244, 498, 811, 949, 23892)]
for T in SETS:
    t, mv = chain(T); R = 8 * T[0] * t; m = T[0]
    f = next(i for i, d in enumerate(T) if (8 * d * t) % 8 == 1) if mv else None
    laps = [floor(d * t) for d in T]
    gaps = [round(T[i] / T[i - 1], 2) for i in range(1, 7)]
    splits = []
    for gi in range(1, 7):
        top = T[gi - 1]; G = [F(g) for g in T[gi:]]
        for k in (0, 1):
            lo, hi = F(8 * k + 1, m), F(8 * k + 7, top)
            if lo <= hi and lo <= R <= hi and all(nd(g * t) >= E8 for g in T[gi:]): splits.append((gi, k))
    print(T, "R* = %s (%.4f), flank rank %s, laps %s, gaps %s" % (R, float(R), f, laps, gaps))
    print("    chain:", mv, "  landing inside the slow block of split(s) (slow = ranks < gi, lap k):", splits)
