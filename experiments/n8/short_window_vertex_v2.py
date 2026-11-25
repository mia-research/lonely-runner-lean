"""E943's 2,251 not-understood members, per member (2026-11-25).  Exact Fractions; the cascade decides every path.
Members and classes from short_window_classes_v1_part*.pkl (N = 726, Z = 1,525).  For each member and each targeted
move (raise x unless x is reading 1; lower y), the largest eps in [0, 10^-6] keeping the path (80 halvings; 'open' if
10^-6 keeps it), the window's length there, and the closing pair (path state index, reading, edge) with whether it is
one of the member's own near-coincidences (relative gap below 10^-7).  Each member is then sorted:
  R1  the window grows by more than a factor 10 inside its own path under one targeted move (as the 18,851);
  R2  it does not, and every applicable move is closed by a pair (path state, reading edge) on the path;
  R3  it does not, and some move is open to 10^-6: the window is then at least 10^-6 * a / 10 relative, not short
      against the move used;
  R0  L0 = 0 (a single-point window), counted apart.
"""
import pickle, sys, glob
from fractions import Fraction as Fr
from collections import Counter
exec(open('short_window_vertex_v1.py').read().split("rec = pickle.load(open('/Users/trentpalelei")[0])
rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
mem = []
for f in sorted(glob.glob('short_window_classes_v1_part*.pkl')): mem += pickle.load(open(f, 'rb'))
mem.sort()
step = int(sys.argv[1]); off = int(sys.argv[2])
c = Counter(); out = []; shown = set()
for (idx, cls, xi, j, yi, jp, a, b, kept, keptS, Lmax, best, why) in mem[off::step]:
    rs = sorted(Fr(x) for x in rec[idx][1]); T0, sig0 = path_sig(rs); L0 = b - a
    C = coinc(rs)
    Lw = lambda rr: Fr(8 * jp - 1, 8) / rr[yi] - Fr(8 * j + 1, 8) / rr[xi]
    res = []
    for which, q, sign in (('raise x', xi, 1), ('lower y', yi, -1)):
        if q == 0: continue
        def mv(eps, q=q, sign=sign): nw = list(rs); nw[q] = rs[q] * (1 + sign * eps); return nw
        ok = lambda nw: sorted(nw) == nw and path_sig(nw)[1] == sig0
        hi = Fr(1, 10 ** 6)
        if ok(mv(hi)): res.append((which, 'open', Lw(mv(hi)), None, None)); continue
        lo = Fr(0)
        for _ in range(80):
            mid = (lo + hi) / 2
            if ok(mv(mid)): lo = mid
            else: hi = mid
        nw = mv(lo); Cl = coinc(nw, Fr(1, 10 ** 20))
        closing = sorted([p for p in Cl if not (gap_of(rs, p) == 0)], key=lambda p: gap_of(nw, p))
        p = closing[0] if closing else None
        res.append((which, 'closed', Lw(nw), lo, p))
    Lbest = max(r[2] for r in res)
    if L0 == 0: R = 'R0'
    elif Lbest > 10 * L0: R = 'R1'
    elif all(r[1] == 'closed' for r in res): R = 'R2'
    else: R = 'R3'
    c[(cls, R)] += 1
    for which, kind, Ln, lo, p in res:
        if kind == 'closed':
            c[(cls, R, which, 'closed by a member near-coincidence' if p in C else ('closed by a pair not below 10^-7 in the member' if p else 'closed, no pair named'))] += 1
            if p: c[(cls, R, which, 'closing reading is the moved one' if p[1] == (xi if which == 'raise x' else yi) else 'closing reading is another')] += 1
    c[(cls, R, 'L0/a >= 10^-7' if L0 / a >= B7 else ('L0/a in [10^-8, 10^-7)' if L0 / a >= Fr(1, 10 ** 8) else 'L0/a < 10^-8'))] += 1
    if R == 'R0':
        c[(cls, R, 'some move gives positive length on the path' if Lbest > 0 else 'no move gives positive length')] += 1
    out.append((idx, cls, R, L0, a, [(w, k, Ln, lo, p) for w, k, Ln, lo, p in res], sorted(C)))
    if (cls, R) not in shown:
        shown.add((cls, R))
        print('first of', cls, R, '| E340 index', idx, '| x rank', xi + 1, 'lap', j, '| y rank', yi + 1, 'lap', jp, '| L0/a ~ %.3e' % float(L0 / a), '| near-coincidences', [(pi, pq + 1, str(pe)) for pi, pq, pe in sorted(C)])
        for w, k, Ln, lo, p in res: print('    ', w, k, '| length there ~ %.3e' % float(Ln), '| eps ~', None if lo is None else '%.3e' % float(lo), '| closing', None if p is None else (p[0], p[1] + 1, str(p[2])))
pickle.dump(out, open('short_window_vertex_v2_part%d.pkl' % off, 'wb'))
for k, val in sorted(c.items(), key=str): print(val, '|', k)
