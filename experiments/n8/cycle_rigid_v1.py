"""E951: the 625 crossers of the 2,607 with no rigid pin (pin_ident_v1: 615 + 10).  Exact Fractions.
For each attaining reading k, every combination of identifications of x_P and x_A (pin_ident_v1.idents) gives an escape row.
k is BLOCKED if, under every combination, the escape row is a pin (c r_j <= 0, c > 0) or closes a cycle with product < 1 in the
ratio graph of the closed path cell (cert_cycle_v2).  A crosser is certified if some attaining reading is BLOCKED.
Recorded for blocked readings with one combination (rigid): the shortest cycle's escape pair (roles), the cell row's state,
kind and its two readings, and the two bounds on the pair's ratio (escape needs, cell allows)."""
import sys
from fractions import Fraction as Fr
from collections import Counter
src = open('cert_cycle_v2.py').read()
exec(src.split("step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()\n")[0])
def idents(x, rs):
    return [(j + 1, x / rs[j]) for j in range(7) if (x / rs[j]).numerator < 2000 and (x / rs[j]).denominator < 2000]
def esc_row(jA, qA, jP, qP, side):
    v = [Fr(0)] * 6; rhs = Fr(0); sgn = 1 if side == 'below' else -1
    for j_, q_, s_ in ((jA, qA, sgn), (jP, qP, -sgn)):
        if j_ == 1: rhs -= s_ * q_
        else: v[j_ - 2] += s_ * q_
    return v, rhs
step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()
for idx, R0, closers, cls, att in rows[off::step]:
    if not att or any(cls[k] != 'X' for k in att): continue
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E); o = rs.index(path[-1]) + 1
    fs = []
    for k1 in att:
        f = facing(rs, T, k1 - 1)
        if f is None or f[0] == 0: fs = None; break
        if ident(f[1], rs)[0] is None or ident(f[2], rs)[0] is None: fs = None; break
        fs.append((k1, f))
    if fs is None: continue
    rigidpin = False
    for k1, (d, xP, xA, side) in fs:
        IP, IA = idents(xP, rs), idents(xA, rs)
        if len(IP) == 1 and len(IA) == 1 and IP[0][0] == IA[0][0]: rigidpin = True
    if rigidpin: continue
    A, b, tag = cell_exact(rs); Ec = to_edges(A, b, tag, Counter(), 'x')
    role = lambda q1, k1: 'k' if q1 == k1 else ('c' if q1 in closers else ('o' if q1 == o else ('1' if q1 == 1 else 'x')))
    blocked_any = False; desc = []
    for k1, (d, xP, xA, side) in fs:
        IP, IA = idents(xP, rs), idents(xA, rs); allb = True; cyc_d = None
        for jP, qP in IP:
            for jA, qA in IA:
                v, rhs = esc_row(jA, qA, jP, qP, side); w = [-rhs] + v
                if any(x > 0 for x in w) and not any(x < 0 for x in w): continue
                E1 = dict(Ec)
                for key, val in to_edges([v], [rhs], [('escape', k1, side)], Counter(), 'x').items():
                    if key not in E1 or val[0] < E1[key][0]: E1[key] = val
                cy = sorted([x for x in cycles(E1) if x[0] < 1], key=lambda x: (len(x[1]), x[0]))
                if not cy: allb = False; break
                cyc_d = (cy[0], {key: E1[key][0] for key in E1})
            if not allb: break
        if allb:
            blocked_any = True
            if len(IP) == 1 and len(IA) == 1 and cyc_d is not None:
                (p, cyc, es), W = cyc_d
                ee = [e for e in es if e[2][0] == 'escape'][0]; ce = [e for e in es if e[2][0] != 'escape']
                if len(cyc) == 2:
                    R, kd, qs = ce[0][2]; st = 'R=1' if R == 1 else ('R=9' if R == 9 else ('ph1' if R < 9 else 'ph2'))
                    pair = ''.join(sorted(role(q + 1, k1) for q in cyc))
                    c[('rigid 2-cycle', 'pair roles', pair, 'cell row', st, kd)] += 1
                    desc.append(('k', k1, 'P', IP[0][0], str(IP[0][1]), 'A', IA[0][0], str(IA[0][1]), side, 'cycle', [(a_ + 1, b_ + 1, str(W[(a_, b_)]), tg if tg[0] == 'escape' else (str(tg[0]), tg[1], tg[2])) for a_, b_, tg in es], 'product', str(p)))
                else: c[('rigid cycle length', len(cyc))] += 1
            else: c[('blocked under every identification', len(IP), len(IA))] += 1
    c[('crosser certified (some attaining reading blocked)', blocked_any)] += 1
    if not blocked_any: print('NOT CERTIFIED', idx, att, flush=True)
    for dd in desc[:1]: print('EX', idx, dd, flush=True)
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
