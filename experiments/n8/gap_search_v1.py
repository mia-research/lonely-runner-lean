# E644: search for a six-reading set C (whole numbers, gcd 1) whose own windows leave a gap in [3/8, y0].  Float SCREEN (steers only, rule 15); every flagged set is re-checked exactly (Fractions) with more shifts.
# usage: H count seed [NSHIFT]
import sys, math, random, itertools
import numpy as np
from fractions import Fraction as F
from classes_lib_v1 import clear_iv, meet
H = int(sys.argv[1]); COUNT = int(sys.argv[2]); SEED = int(sys.argv[3]); NS = int(sys.argv[4]) if len(sys.argv) > 4 else 12
def windows(core):
    g = 0
    for d in core: g = math.gcd(g, d)
    T = F(1, g)
    J = clear_iv(F(core[0]), T)
    for s in core[1:]:
        J = meet(J, clear_iv(F(s), T))
        if not J: return None, T
    J = [(lo, hi) for lo, hi in J if hi >= lo and lo > 0]
    return (J or None), T
def screen(J, T, ns, exact=False):
    w = max(hi - lo for lo, hi in J); y0 = 1 / (4 * w)
    if exact:
        iv = []
        for lo, hi in J:
            for n in range(ns + 1):
                a_, b_ = lo + n * T, hi + n * T; k = 0
                while F(8 * k + 1, 8) / b_ <= y0:
                    iv.append((F(8 * k + 1, 8) / b_, F(8 * k + 7, 8) / a_)); k += 1
        iv.sort(); cur = F(3, 8)
        for lo, hi in iv:
            if hi <= cur: continue
            if lo > cur: return (cur, lo), y0
            cur = hi
            if cur >= y0: return None, y0
        return ((cur, y0) if cur < y0 else None), y0
    A = []; B = []; y0f = float(y0)
    for lo, hi in J:
        for n in range(ns + 1):
            a_, b_ = float(lo + n * T), float(hi + n * T)
            kmax = int(y0f * b_ - 0.125) + 1
            if kmax < 0: continue
            k = np.arange(0, kmax + 1)
            A.append((k + 0.125) / b_); B.append((k + 0.875) / a_)
    A = np.concatenate(A); B = np.concatenate(B); o = np.argsort(A); A = A[o]; B = B[o]
    cm = np.maximum.accumulate(B)
    if A[0] > 0.375 + 1e-12: return (0.375, A[0]), y0
    bad = np.where(A[1:] > cm[:-1] + 1e-12)[0]
    bad = [i for i in bad if cm[i] < y0f]
    if bad: return (cm[bad[0]], A[bad[0] + 1]), y0
    if cm[-1] < y0f: return (cm[-1], y0f), y0
    return None, y0
rnd = random.Random(SEED); tested = flagged = 0; confirmed = []
while tested < COUNT:
    C = tuple(sorted(rnd.sample(range(1, H + 1), 6)))
    g = 0
    for d in C: g = math.gcd(g, d)
    if g != 1: continue
    tested += 1
    J, T = windows(C)
    if J is None: print('NO WINDOW', C); continue
    gap, y0 = screen(J, T, NS)
    if gap:
        flagged += 1
        gx, _ = screen(J, T, 60, exact=True)
        if gx: confirmed.append((C, str(gx[0]), str(gx[1]), str(y0)))
print('H', H, 'tested', tested, 'float-flagged', flagged, 'exact gaps (shifts<=60)', len(confirmed)); [print(c) for c in confirmed[:10]]
