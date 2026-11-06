# E824: the gaps of the first window A (least lo, shift 0): for each gap (b_k, a_{k+1}) the least number of pieces of the OTHER windows/shifts covering it (greedy, exact).
import sys, pickle
from multiprocessing import Pool
from fractions import Fraction as F
from chain_lo_v1 import win
def gaps(core):
    J, T = win(core)
    jw = max(J, key=lambda w: w[1] - w[0]); y0 = 1 / (4 * (jw[1] - jw[0]))
    A = min(J)  # (lo_min, hi) at shift 0
    others = []
    for lo, hi in J:
        for n in range(0, 80):
            d = F(n) * T
            if (lo, hi, n) == (A[0], A[1], 0) or hi + d == 0: continue
            k = 0
            while F(8 * k + 1, 8) / (hi + d) <= y0 * 2:
                others.append((F(8 * k + 1, 8) / (hi + d), F(8 * k + 7, 8) / (lo + d))); k += 1
    others.sort()
    ms = []; k = 0
    while True:
        b = F(8 * k + 7, 8) / A[0]; a_next = F(8 * k + 9, 8) / A[1]
        if b >= y0: break
        if a_next <= b: k += 1; continue
        cur = b; m = 0; i = 0; best = None
        while cur < a_next:
            while i < len(others) and others[i][0] <= cur:
                if best is None or others[i][1] > best: best = others[i][1]
                i += 1
            if best is None or best <= cur: m = None; break
            cur = best; m += 1
        ms.append((k, b, a_next, m)); k += 1
    return core, A, y0, ms
if __name__ == '__main__':
    cores = [tuple(int(x) for x in l.split(',')) for l in open('core_cover_cores.txt') if l.strip()]
    with Pool(10) as p: res = p.map(gaps, cores)
    pickle.dump(res, open('chain_gaps_v1.pkl', 'wb'))
    import collections
    cnt = collections.Counter(); tot = 0
    for core, A, y0, ms in res:
        for k, b, a, m in ms: cnt[m] += 1
    print('cores', len(res), 'gaps', sum(cnt.values()), 'fillers needed per gap (count of gaps):', sorted(cnt.items(), key=lambda x: (x[0] is None, x[0])))
    for core, A, y0, ms in res[:3]: print(core, 'A', A, 'y0', y0, 'fillers per gap by lap k:', [m for k, b, a, m in ms])
