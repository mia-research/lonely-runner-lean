# E645: same greedy chain as gen_real_core_v1.cert, by a sorted sweep (exact Fractions).
import math
from fractions import Fraction as F
from classes_lib_v1 import clear_iv, meet
def feats(core):
    g = 0
    for d in core: g = math.gcd(g, d)
    T = F(1, g)
    J = clear_iv(F(core[0]), T)
    for s in core[1:]: J = meet(J, clear_iv(F(s), T))
    J = [(lo, hi) for lo, hi in J if hi >= lo and lo > 0]
    jw = max(J, key=lambda w: w[1] - w[0]); w = jw[1] - jw[0]; y0 = 1 / (4 * w)
    cand = []
    for lo, hi in J:
        for n in range(0, 80):
            d = F(n) * T
            if hi + d == 0: continue
            k = 0
            while F(8 * k + 1, 8) / (hi + d) <= y0 * 2:
                cand.append((F(8 * k + 1, 8) / (hi + d), F(8 * k + 7, 8) / (lo + d))); k += 1
    cand.sort()
    cur = F(3, 8); n = 0; i = 0; best = None
    while True:
        while i < len(cand) and cand[i][0] <= cur:
            if best is None or cand[i][1] > best: best = cand[i][1]
            i += 1
        if best is None or best <= cur: return dict(chain=None, y0=y0, w=w, nw=len(J), T=T)
        cur = best; n += 1
        if cur >= y0: return dict(chain=n, y0=y0, w=w, nw=len(J), T=T)
