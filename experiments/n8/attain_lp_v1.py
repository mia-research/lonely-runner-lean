"""E949: is "some reading attains min B_k" forced by the path cell?  A joint LP per crosser (2026-11-25).
Population: gate crossers (E340) whose attaining set (E945) is all class X.  For each attaining k, attain_pin_v2's facing
ends x_P = q_P r_jP and x_A = q_A r_jA (P the pass set of W_k, A the positions passing every earlier six-window) are
linear in the speeds; k escapes when the facing ends cross (x_P >= x_A if P lies below A, x_P <= x_A if above).
The path cell of the seven readings (short_window_cell_lp_v2.cell: the same setters, laps, readings in the way and
max-exit choices; linear in r_2..r_7) plus "every attaining k escapes" is a float LP feasibility problem (STEERS ONLY,
rule 15; rows tightened by 1e-9 x norm).  Infeasible: within the cell, with these facing-end identities, the readings
cannot all escape together.  Feasible: exact points p = member + lam (opt - member) are built in Fractions, lam from 1 - 10^-6
down, and the EXACT test is run at each (crosser_equality_v1's classes and bmove's B_k): min_k B_k > 8 end?"""
import pickle, glob, sys
import numpy as np
from scipy.optimize import linprog
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
exec(open('attain_pin_v2.py').read().split("step, off = int")[0])
exec(open('neighbour_mover_v1.py').read().split("rec = pickle.load(open('/Users")[0])
src = open('short_window_cell_lp_v2.py').read(); exec('def cell' + src.split('def cell')[1].split('step = int')[0])
def facing(rs, T, k):
    six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]
    ws = windows(six, E, T1); n = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y); a, b = ws[n][0], ws[n][1]
    hi = rs[k + 1] if k < 6 else ((a + b) / (b - a) + 1) / (8 * b) + 1
    P = [(l, h) for l, h, m in passes(a, b, lo, hi)]; A = [(lo, hi)]
    for jj in range(n):
        if not A: break
        A = passes_in(ws[jj][0], ws[jj][1], A)
    if not P or not A: return None
    best = None
    for lp, hp in P:
        for la, ha in A:
            if hp <= la: d, xP, xA, side = la - hp, hp, la, 'below'
            elif ha <= lp: d, xP, xA, side = lp - ha, lp, ha, 'above'
            else: d, xP, xA, side = 0, None, None, 'meet'
            if best is None or d < best[0]: best = (d, xP, xA, side)
    return best
def minB_vs_end(rs):
    T, path = cascade(rs, E)
    if 8 * T < 9: return None
    end = min((floor(x * T + E) + 1 - E) / x for x in rs); Bs = []
    for kk in range(1, 7):
        six = rs[:kk] + rs[kk + 1:]; Bk = bmove(six, rs[kk - 1], rs[kk + 1] if kk < 6 else None)[0]
        if isinstance(Bk, Fr): Bs.append(Bk)
    return min(Bs) > 8 * end, min(Bs), 8 * end, 8 * T
step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()
for idx, R0, closers, cls, att in rows[off::step]:
    if not att or any(cls[k] != 'X' for k in att): continue
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E)
    Am, bm = cell(rs); Ar = list(Am); br = list(bm); ok = True; sames = 0
    for k1 in att:
        k = k1 - 1; f = facing(rs, T, k)
        if f is None or f[0] == 0: ok = False; break
        d, xP, xA, side = f; jP, qP = ident(xP, rs); jA, qA = ident(xA, rs)
        if jP is None or jA is None: ok = False; break
        v = np.zeros(6); rhs = 0.0
        # escape: below -> q_P r_jP - q_A r_jA >= 0 -> q_A r_jA - q_P r_jP <= 0 ; above -> q_P r_jP - q_A r_jA <= 0
        sgn = 1 if side == 'below' else -1
        for j_, q_, s_ in ((jA, qA, sgn), (jP, qP, -sgn)):
            if j_ == 1: rhs -= s_ * float(q_)
            else: v[j_ - 2] += s_ * float(q_)
        if jA == jP: sames += 1
        Ar.append(v); br.append(rhs)
    if not ok: c[('skipped: facing ends not identified',)] += 1; continue
    Ar = np.array(Ar); br = np.array(br) - 1e-9 * np.linalg.norm(Ar, axis=1)
    bounds = [(1.0, 10 * float(rs[q])) for q in range(1, 7)]
    res = linprog(np.zeros(6), A_ub=Ar, b_ub=br, bounds=bounds, method='highs')
    key = ('attaining', len(att), 'same-reading pins', sames)
    if res.status == 2: c[key + ('LP infeasible',)] += 1; continue
    if res.status != 0: c[key + ('LP status', res.status)] += 1; continue
    opt = [Fr(1)] + [Fr(float(v)) for v in res.x]; found = None
    for lam in [1 - Fr(1, 10 ** 6), 1 - Fr(1, 10 ** 3), Fr(9, 10)]:
        p = [rs[q] + lam * (opt[q] - rs[q]) for q in range(7)]
        if sorted(p) != p: continue
        r = minB_vs_end(p)
        if r is None: continue
        if r[0]: found = (lam, r, p); break
    if found:
        lam, r, p = found
        c[key + ('LP feasible', 'EXACT: min B_k > 8 end at a point')] += 1
        print('ALL ESCAPE | E340 index', idx, '| lam', lam, '| R*', r[3], '| 8 end', r[2], '| min B_k', r[1], '| readings', [str(x) for x in p], flush=True)
    else:
        c[key + ('LP feasible', 'no exact all-escape point at the tried lam')] += 1
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
