"""E947: the one class-N reading whose island does not meet W_k's pass set in path_islands_v3 (2026-11-25).  Exact.
Locates it, lists its escaping intervals (the walk's A intersected with W_k's pass set, all of them, no cap), and for
each: whether it lies in the island, whether the cascade there crosses the gate, and the island it lies in (the run of
gate-crossing positions around it, bisected), against the actual position's island.
"""
import pickle, glob
from fractions import Fraction as Fr
exec(open('path_islands_v2.py').read().split("step = int(sys.argv[1])")[0])
def island(six, v, lo, hi):
    g = lambda u: gate(sorted(six + [u]))
    a = v; d = (hi - lo) / 1000
    while a - d > lo and g(a - d): a -= d
    l = edge(g, a, max(lo, a - d)) if a - d > lo else lo
    b = v
    while b + d < hi and g(b + d): b += d
    r = edge(g, b, min(hi, b + d)) if b + d < hi else hi
    return l, r
for idx, R0, closers, cls, att in rows:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, _ = cascade(rs, E)
    for k in range(1, 7):
        if cls[k + 1] != 'N': continue
        six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]; hi = rs[k + 1] if k < 6 else 2 * rs[6]
        ws = windows(six, E, T1); nW = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y); a, b = ws[nW][0], ws[nW][1]
        hiP = hi if k < 6 else ((a + b) / (b - a) + 1) / (8 * b) + 1
        PW = [(l, h) for l, h, m in passes(a, b, lo, hiP)]
        L, R = island(six, rs[k], lo, hi)
        if any(L < h and l < R for l, h in PW[:40]): continue
        A = list(PW)
        for jj in range(nW): A = passes_in(ws[jj][0], ws[jj][1], A)
        print('E340 index', idx, '| N reading', k + 1, '| segment', (float(lo), float(hi)), '| actual island (floats, steer only)', (float(L), float(R)), '| pass intervals of W_k', len(PW), '| escaping intervals', len(A))
        for l, h in A:
            v = (l + h) / 2; Li, Ri = island(six, v, lo, hi)
            print('   escaping interval (floats) (%.9f, %.9f) | index among pass intervals %d | crosses the gate %s | its island (%.9f, %.9f) | same island as the actual: %s' % (float(l), float(h), next(i for i, (x, y) in enumerate(PW) if x <= l and h <= y), gate(sorted(six + [v])), float(Li), float(Ri), (Li, Ri) == (L, R)))
