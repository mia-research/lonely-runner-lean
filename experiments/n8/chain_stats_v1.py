# E644: for every gcd-1 six-subset of [1, N] (float screen; steers only): widest window w, y0 = 1/(4w), greedy chain length over [3/8, y0] with <= 12 shifts.  Reports the extremes and y0 against max(C) and against the number of windows.
import sys, math, itertools, collections
import numpy as np
N = int(sys.argv[1]); sys.argv = ['x', '1', '1', '1']
exec(open('gap_search_v1.py').read().split('rnd = random.Random')[0])
def chain_len(J, T, ns=12):
    w = max(hi - lo for lo, hi in J); y0 = float(1 / (4 * w)); iv = []
    for lo, hi in J:
        for n in range(ns + 1):
            a_, b_ = float(lo + n * T), float(hi + n * T)
            kmax = int(y0 * b_ - 0.125) + 1
            for k in range(0, kmax + 1): iv.append(((k + .125) / b_, (k + .875) / a_))
    iv.sort(); cur = .375; cnt = 0; i = 0
    while cur < y0:
        best = cur
        while i < len(iv) and iv[i][0] <= cur + 1e-12:
            best = max(best, iv[i][1]); i += 1
        if best <= cur: return None, y0
        cur = best; cnt += 1
    return cnt, y0
rows = []
for C in itertools.combinations(range(1, N + 1), 6):
    g = 0
    for d in C: g = math.gcd(g, d)
    if g != 1: continue
    J, T = windows(C); cl, y0 = chain_len(J, T)
    rows.append((C, len(J), cl, y0))
cl = [r[2] for r in rows]; ok = [r for r in rows if r[2] is not None]
print('N', N, 'sets', len(rows), 'chain failures', len(rows) - len(ok), 'max chain', max(r[2] for r in ok), 'dist', sorted(collections.Counter(r[2] for r in ok).items())[:14])
print('max y0', max(r[3] for r in ok), 'y0/max(C) max', max(r[3] / r[0][-1] for r in ok), 'y0/max(C) min', min(r[3] / r[0][-1] for r in ok))
print('longest chains', [(r[0], r[2], round(r[3], 2)) for r in sorted(ok, key=lambda r: -r[2])[:5]])
print('largest y0', [(r[0], r[2], round(r[3], 2)) for r in sorted(ok, key=lambda r: -r[3])[:5]])
