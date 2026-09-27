"""E157: the composed regime for the sets the single grid-class reference misses: split at a gap into slow S (spread
<= 7) and fast G; slow readings on lap k (k = 0, 1; their common block); fast readings on the laps of a grid class through
a fast reading j at scale s_j/m (m <= 8, c in {1,3,5,7}); decided exactly by 1-D Helly (lonely_eight_of_pairwise_laps).
Applied to the uncovered sets of casec_gridclass_v1.  Exact."""
import ast
from fractions import Fraction as F
from math import floor, ceil
def works_composed(T, gi, k, j, m, c):
    s = [F(d) for d in T]; lam = s[j] / m; opts = []
    for i, x in enumerate(s):
        if i < gi: opts.append((x, [k])); continue
        o = []
        for n in {floor(x / lam), ceil(x / lam)}:
            if n < 1: continue
            kk0 = (c * n) // 8
            for kk in ((kk0 - 1, kk0) if (c * n) % 8 == 0 else (kk0,)):
                if kk >= 0: o.append(kk)
        if not o: return False
        opts.append((x, o))
    cands = sorted({F(8 * kk + 1) / x for x, o in opts for kk in o})
    return any(all(any(F(8 * kk + 1) / x <= R <= F(8 * kk + 7) / x for kk in o) for x, o in opts) for R in cands)
def composed(T):
    for gi in range(1, 7):
        if T[gi - 1] > 7 * T[0]: break
        for k in (0, 1):
            for j in range(gi, 7):
                for m in range(1, 9):
                    for c in (1, 3, 5, 7):
                        if works_composed(T, gi, k, j, m, c): return (gi, k, j, m, c)
    return None
line = [l for l in open('casec_gridclass_v1.out') if l.startswith('P2')][0]
U = ast.literal_eval(line.split('uncovered (m<=8): ')[1].split(' ', 1)[1])
for T in U: print(T, "->", composed(T))
