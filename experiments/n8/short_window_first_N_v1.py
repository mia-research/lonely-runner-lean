"""The first member of E943's 726 (class N of short_window_classes_v1) through the cascade (2026-11-25).  Exact Fractions.
E340 index 1072.  For the path's states t_0 = 1/8, ..., T, and each reading q, the gap from q*t to q's nearest zone edge
(m - 1/8 or m + 1/8), relative: delta = |q t - edge| / (q t).  A small delta is a near-coincidence of a path state with
a zone edge.  Then the targeted move (reading x raised, relative eps) is bisected to the eps at which the path changes,
and the first differing step is shown: the state, the readings in the way, and their exits, before and after.
"""
import pickle
from fractions import Fraction as Fr
from math import floor
exec(open('short_window_v1.py').read().split("rec = pickle.load(open('/Users")[0])

def near(rs, bound):
    st = states(rs); out = []
    for i, t in enumerate(st):
        for q, r in enumerate(rs):
            x = r * t; m = round(x)
            for e in (m - E, m + E):
                d = abs(x - e) / x
                if 0 < d < bound: out.append((d, i, q + 1, e, 'in the way' if blocked(r, t) else 'clear'))
                if d == 0: out.append((d, i, q + 1, e, 'on the edge'))
    return sorted(out)

def step_detail(rs, t):
    b = [(q + 1, nxt(r, t)) for q, r in enumerate(rs) if blocked(r, t)]
    return b

rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
rs = sorted(Fr(x) for x in rec[1072][1]); six = rs[:6]
T0, sig0 = path_sig(rs); st = states(rs)
print('readings (floats, steer only)', [round(float(q), 6) for q in rs])
print('path (rank, lap)', sig0, '| R*', 8 * T0)
ws = windows(six, E, T1); Bk, n = bmove(six, rs[5], None)
i = min(range(n + 1), key=lambda q: ws[q][1] - ws[q][0]); a, b, o = ws[i]
(xi, j), (yi, jp) = edges(six, a, b)[0][0], edges(six, a, b)[1][0]
print('window', i + 1, 'of the six: exit of rank', xi + 1, 'lap', j, '-> entry of rank', yi + 1, 'lap', jp, '| state index of a:', st.index(a) if a in st else None)
print('near-coincidences of path states with zone edges, relative gap below 10^-6:')
for d, si, q, e, kind in near(rs, Fr(1, 10 ** 6)):
    print('   state %2d (R ~ %.6f) | rank %d | edge %s | gap ~ %.3e | %s' % (si, float(8 * st[si]), q, e, float(d), kind))
lo, hi = Fr(1, 10 ** 8), Fr(1, 10 ** 7)
def mv(eps): new = list(rs); new[xi] = rs[xi] * (1 + eps); return new
assert path_sig(mv(lo))[1] == sig0 and path_sig(mv(hi))[1] != sig0
for _ in range(60):
    mid = (lo + hi) / 2
    if path_sig(mv(mid))[1] == sig0: lo = mid
    else: hi = mid
print('raise rank', xi + 1, ': path kept up to eps ~ %.6e, changes by eps ~ %.6e' % (float(lo), float(hi)))
L = lambda r: Fr(8 * jp - 1, 8) / r[yi] - Fr(8 * j + 1, 8) / r[xi]
print('   window length: member ~ %.6e | at the kept limit ~ %.6e' % (float(L(rs)), float(L(mv(lo)))))
s1 = path_sig(mv(hi))[1]; p = next(q for q in range(min(len(sig0), len(s1))) if sig0[q] != s1[q]) if sig0[:len(s1)] != s1[:len(sig0)] else min(len(sig0), len(s1))
print('   first differing step', p, '| kept', sig0[p:p + 3], '| changed', s1[p:p + 3])
for lab, r in (('kept', mv(lo)), ('changed', mv(hi))):
    t = states(r)[p]
    print('   %s: state R ~ %.9f | in the way (rank, exit R~): %s' % (lab, float(8 * t), [(q, round(float(8 * e), 9)) for q, e in step_detail(r, t)]))
print('   near-coincidences at the kept limit, relative gap below 10^-9:')
for d, si, q, e, kind in near(mv(lo), Fr(1, 10 ** 9)):
    print('      state %2d | rank %d | edge %s | gap ~ %.3e | %s' % (si, q, e, float(d), kind))
