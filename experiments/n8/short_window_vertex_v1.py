"""E943's not-understood members: what closes the window's opening (2026-11-25).  Exact Fractions; the cascade decides.
For every E340 member whose fastest-reading walk is skipped (E941/E943, 21,102), with class G / N / Z from
short_window_classes_v1 (replayed with the same seeded draws):
  nc = number of near-coincidences on the path: a pair (path state t_i, reading q) with 0 < |q t_i - edge|/(q t_i) <
       10^-7, edge = m - 1/8 or m + 1/8; plus ties (gap 0 where q is not the setter of that state).  The window itself
       is one such pair when its left end is a state (reading y's entry just after the state).
For classes N and Z, each targeted move (raise x unless x is reading 1; lower y) is bisected on eps in [0, 10^-6]
(80 halvings) to the largest eps that keeps the path; at that limit the pair that closes (smallest nonzero gap) is
named, with whether it was one of the member's own near-coincidences, and the window's growth factor there.
"""
import pickle, random, sys
from fractions import Fraction as Fr
from math import floor
from collections import Counter
exec(open('short_window_v1.py').read().split("rec = pickle.load(open('/Users")[0])
B7 = Fr(1, 10 ** 7)

def coinc(rs, bound=B7):
    T, path = cascade(rs, E); t = E; st = [(t, None)]
    for s in path:
        lap = floor(s * t + E); t = (lap + E) / s; st.append((t, rs.index(s)))
    out = set()
    for i, (t, setter) in enumerate(st):
        for q, r in enumerate(rs):
            x = r * t; m = round(x)
            for e in (m - E, m + E):
                d = abs(x - e) / x
                if d == 0 and (q == setter or (i == 0 and q == 0)): continue
                if d < bound: out.add((i, q, e))
    return out

def gap_of(rs, pair):
    i, q, e = pair; t = states(rs)[i]; x = rs[q] * t
    return abs(x - e) / x

rec = pickle.load(open('/Users/trentpalelei/Desktop/Math Ex/LonelyRunner/experiments/nN/redo/disc_records_v1.pkl', 'rb'))
step = int(sys.argv[1]); off = int(sys.argv[2]); random.seed(off)
c = Counter(); first = set()
for idx in range(off, len(rec), step):
    r = rec[idx]
    rs = sorted(Fr(x) for x in r[1]); six = rs[:6]
    Bk, n = bmove(six, rs[5], None)
    if Bk != 'skipped': continue
    ws = windows(six, E, T1)
    i = min(range(n + 1), key=lambda q: ws[q][1] - ws[q][0]); a, b, o = ws[i]
    ex, en = edges(six, a, b)
    if not ex or not en: continue
    (xi, j), (yi, jp) = ex[0], en[0]
    T0, sig0 = path_sig(rs); L0 = b - a; Lmax = L0; kept = 0
    for d in range(24):
        s = random.choice([7, 8, 9, 10])
        new = [rs[0]] + [x * (1 + Fr(random.randint(-1000, 1000), 1000 * 10 ** s)) for x in rs[1:]]
        if sorted(new) != new: continue
        T1n, sig1 = path_sig(new)
        if sig1 != sig0: continue
        kept += 1
        Ln = Fr(8 * jp - 1, 8) / new[yi] - Fr(8 * j + 1, 8) / new[xi]
        if Ln > Lmax: Lmax = Ln
    cls = 'G' if kept and Lmax > 10 * L0 else ('N' if kept else 'Z')
    C = coinc(rs); nc = len(C)
    c[(cls, 'members')] += 1
    c[(cls, 'near-coincidences on the path', nc if nc < 8 else '8+')] += 1
    if cls == 'G': continue
    Lw = lambda rr: Fr(8 * jp - 1, 8) / rr[yi] - Fr(8 * j + 1, 8) / rr[xi]
    bestf = None; res = []
    for which, q, sign in (('raise x', xi, 1), ('lower y', yi, -1)):
        if q == 0: continue
        def mv(eps, q=q, sign=sign): nw = list(rs); nw[q] = rs[q] * (1 + sign * eps); return nw
        ok = lambda nw: sorted(nw) == nw and path_sig(nw)[1] == sig0
        hi = Fr(1, 10 ** 6)
        if ok(mv(hi)): res.append((which, 'open beyond 10^-6', None, None)); f = Lw(mv(hi)); bestf = f if bestf is None or f > bestf else bestf; continue
        lo = Fr(0)
        for _ in range(80):
            mid = (lo + hi) / 2
            if ok(mv(mid)): lo = mid
            else: hi = mid
        nw = mv(lo); f = Lw(nw); bestf = f if bestf is None or f > bestf else bestf
        Cl = coinc(nw, Fr(1, 10 ** 20))
        closing = sorted(Cl - {p for p in Cl if gap_of(nw, p) == 0 and p in C and gap_of(rs, p) == 0}, key=lambda p: gap_of(nw, p))
        if not closing: res.append((which, 'no closing pair named', None, lo)); continue
        p = closing[0]
        res.append((which, 'closing pair is one of the member\'s near-coincidences' if p in C else 'closing pair is new (not below 10^-7 in the member)', p, lo))
    for which, kind, p, lo in res:
        c[(cls, which, kind)] += 1
        if p is not None: c[(cls, which, 'closing pair involves the moved reading' if p[1] == (xi if which == 'raise x' else yi) else 'closing pair involves another reading')] += 1
    if bestf is not None:
        g = (bestf / L0) if L0 else None
        c[(cls, 'growth to the path limit', 'L0 = 0' if L0 == 0 else ('> 10' if g > 10 else '<= 10'))] += 1
    if cls not in first:
        first.add(cls)
        print('first of class', cls, 'E340 index', idx, '| nc', nc, '| pairs', sorted((pi, pq + 1, str(pe)) for pi, pq, pe in C))
        for which, kind, p, lo in res: print('   ', which, '|', kind, '|', None if p is None else (p[0], p[1] + 1, str(p[2])), '| eps limit ~', None if lo is None else '%.3e' % float(lo))
for k, val in sorted(c.items(), key=str): print(val, k)
