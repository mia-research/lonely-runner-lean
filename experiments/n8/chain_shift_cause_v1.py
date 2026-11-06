# E822: when does a core's chain need a shifted piece?  Test of: shift-0 pieces cover y = 3/8 iff max window end hi >= 1/3 (windows lie in [0, T], T = 1/g).
import math
from multiprocessing import Pool
from fractions import Fraction as F
from chain_lo_v1 import win
def zero_shift_chain(core):
    J, T = win(core)
    jw = max(J, key=lambda w: w[1] - w[0]); y0 = 1 / (4 * (jw[1] - jw[0]))
    cand = []
    for lo, hi in J:
        k = 0
        while F(8 * k + 1, 8) / hi <= y0 * 2:
            cand.append((F(8 * k + 1, 8) / hi, F(8 * k + 7, 8) / lo)); k += 1
    cand.sort(); cur = F(3, 8); i = 0; best = None
    while True:
        while i < len(cand) and cand[i][0] <= cur:
            if best is None or cand[i][1] > best: best = cand[i][1]
            i += 1
        if best is None or best <= cur: return False, max(h for _, h in J), T
        cur = best
        if cur >= y0: return True, max(h for _, h in J), T
def job(core):
    ok, mh, T = zero_shift_chain(core); return core, ok, mh, T
if __name__ == '__main__':
    base = [tuple(int(x) for x in l.split(',')) for l in open('core_cover_cores.txt') if l.strip()][:12]
    cores = [tuple(m * x for x in c) for c in base for m in (1, 2, 3, 4, 5)] + [(3, 15, 18, 21, 24, 27), (3, 6, 15, 18, 21, 24)]
    with Pool(10) as p: res = p.map(job, cores)
    agree = 0
    for core, ok, mh, T in res:
        pred = mh >= F(1, 3)
        agree += (pred == ok)
        if pred != ok or T < 1: print(core, 'T', T, 'max hi', mh, 'shift-0 chain exists', ok, 'predicted', pred)
    print('cores', len(res), 'prediction (max hi >= 1/3 iff a shift-0 chain exists) agrees on', agree)
