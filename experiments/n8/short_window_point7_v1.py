"""The 7 single-point windows of E943 that no move opened (short_window_cell_lp_v2: R0, no exact point), through the
cascade (2026-11-25).  Exact Fractions.  For each: readings, path, the point window a = b (exit of x lap j = entry of y
lap j'), the ratio r_y / r_x, which path states equal a or lie near it, exact ties on the path (a non-setter reading
exactly on a zone edge at a state), and which readings are in the way at a.
"""
import pickle, glob
from fractions import Fraction as Fr
from math import floor
exec(open('short_window_vertex_v1.py').read().split("rec = pickle.load(open('/Users/trentpalelei")[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
mem = {}
for f in glob.glob('short_window_classes_v1_part*.pkl'):
    for m in pickle.load(open(f, 'rb')): mem[m[0]] = m
bad = []
for f in glob.glob('short_window_vertex_v2_part*.pkl'):
    for m in pickle.load(open(f, 'rb')):
        if m[2] == 'R0' and max(r[2] for r in m[5]) <= 0: bad.append(m[0])
print(len(bad), 'members:', sorted(bad))
for idx in sorted(bad):
    (_, cls, xi, j, yi, jp, a, b, *_r) = mem[idx]
    rs = sorted(Fr(x) for x in rec[idx][1]); T0, sig = path_sig(rs); st = states(rs)
    print('\nE340 index', idx, '| readings (floats, steer only)', [round(float(q), 9) for q in rs])
    print('   exact readings', [str(q) for q in rs])
    print('   path', sig, '| R*', 8 * T0)
    print('   point window R =', 8 * a, '| exit of rank', xi + 1, 'lap', j, '= entry of rank', yi + 1, 'lap', jp, '| r_y/r_x =', rs[yi] / rs[xi])
    print('   a is a path state:', a in st, '| in the way at a:', [q + 1 for q in range(7) if blocked(rs[q], a)])
    ties = sorted(p for p in coinc(rs, Fr(1, 10 ** 30)))
    print('   exact or near ties on the path (state, rank, edge, gap):', [(i, q + 1, str(e), float(gap_of(rs, (i, q, e)))) for i, q, e in ties])

print('\n--- each tie as an equation, and the smallest opening moves (relative 10^-30) through the cascade ---')
for idx in sorted(bad):
    (_, cls, xi, j, yi, jp, a, b, *_r) = mem[idx]
    rs = sorted(Fr(x) for x in rec[idx][1]); T0, sig = path_sig(rs); st = states(rs)
    setters = [None] + [(q, l) for q, l in sig]
    print('\nE340 index', idx)
    for i, q, e in sorted(coinc(rs, Fr(1, 10 ** 30))):
        if i == 0: print('   tie: t0 = 1/8 and rank %d at edge %s, so r_%d = %s' % (q + 1, e, q + 1, 8 * e))
        else:
            k, l = setters[i]
            print('   tie: state %d = exit of rank %d lap %d = %s/r_%d, rank %d at edge %s, so r_%d / r_%d = %s' % (i, k + 1, l, l + E, k + 1, q + 1, e, q + 1, k + 1, e / (l + E)))
    for which, q, sign in (('raise x', xi, 1), ('lower y', yi, -1)):
        if q == 0: continue
        nw = list(rs); nw[q] = rs[q] * (1 + sign * Fr(1, 10 ** 30))
        T1n, s1 = path_sig(nw); st1 = states(nw)
        p = next((u for u in range(min(len(sig), len(s1))) if sig[u] != s1[u]), min(len(sig), len(s1)))
        print('   %s by 10^-30: path differs at step %d | member %s | moved %s' % (which, p, sig[p:p + 2], s1[p:p + 2]))
        print('      in the way at that state: member %s | moved %s' % ([u + 1 for u in range(7) if blocked(rs[u], st[p])], [u + 1 for u in range(7) if blocked(nw[u], st1[p])]))
        print('      R* member %s ~ %.6f | moved %s ~ %.6f' % (8 * T0, float(8 * T0), 8 * T1n, float(8 * T1n)))
