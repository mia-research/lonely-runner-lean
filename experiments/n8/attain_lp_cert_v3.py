"""v3: as v2, printing the full certificate (rows written out, with their multipliers y) for the first crossers of
each support kind with at most 2 cell rows (argument: how many per kind).
v2: as v1, recording for each certificate the rows it uses: the state of each cell row (R = 8t, phase 1 below 9,
phase 2 from 9), its kind (in the way, clear, max-exit choice, order, lower bound), and whether the row involves an attaining
reading.
E949: exact Farkas certificates for attain_lp_v2's joint infeasibility (2026-11-25).  Exact Fractions for the verdict.
System (closure, all rows non-strict): the seven's path cell (as short_window_cell_lp_v2.cell, written in exact Fractions),
r_q <= r_{q+1}, r_q >= 1, and for every attaining reading k its escape row (facing ends crossed, attain_lp_v1).
Unknowns r_2..r_7 (r_1 = 1).  A x <= b is infeasible iff some y >= 0 has y^T A = 0 and y^T b < 0.  A float LP
(min y^T b, A^T y = 0, sum y = 1, y >= 0; STEERS ONLY) gives a support S; the exact system A_S^T y = 0, sum y = 1 is
solved in Fractions on S (least-norm not needed: a basic solution), and the certificate is accepted only if the exact
y >= 0, y^T A = 0 and y^T b < 0 all hold.  Infeasibility of the CLOSURE implies infeasibility of the strict system."""
import pickle, glob, sys
import numpy as np
from scipy.optimize import linprog
from fractions import Fraction as Fr
from math import floor, ceil
from collections import Counter
src = open('attain_lp_v2.py').read()
exec(src.split("step, off = int(sys.argv[1]), int(sys.argv[2]); SHOW = int(sys.argv[3]); c = Counter()\n")[0])
def cell_exact(rs):
    T, path = cascade(rs, E); t = E; st = [(E, 0, E)]
    for s in path:
        lap = floor(s * t + E); k = rs.index(s); t = (lap + E) / s; st.append((t, k, lap + E))
    A = []; b = []; tag = []
    cur = {}
    def row(coef, const=Fr(0)):
        tag.append((cur.get('R'), cur.get('kind'), tuple(sorted(q + 1 for q in coef))))
        v = [Fr(0)] * 6; rhs = Fr(const)
        for q, a in coef.items():
            if q == 0: rhs -= Fr(a)
            else: v[q - 1] += Fr(a)
        A.append(v); b.append(rhs)
    for i, (t, k, cc) in enumerate(st):
        blk = []; cur['R'] = 8 * t
        for q in range(7):
            if q == k and (i > 0 or q == 0): continue
            x = rs[q] * t
            cur['kind'] = 'in the way' if blocked(rs[q], t) else 'clear'
            if blocked(rs[q], t):
                m = round(x); blk.append((q, ceil(x - E)))
                row({k: m - E, q: -cc}); row({q: cc, k: -(m + E)})
            else:
                m = floor(x - E)
                row({k: m + E, q: -cc}); row({q: cc, k: -(m + 1 - E)})
        if i + 1 < len(st):
            _, kn, cn = st[i + 1]; cur['kind'] = 'max-exit'
            for q, lq in blk:
                if q != kn: row({kn: lq + E, q: -cn})
    cur['R'] = None; cur['kind'] = 'order'
    for q in range(6): row({q: 1, q + 1: -1})
    cur['kind'] = 'lower bound'
    for q in range(1, 7): row({q: -1}, Fr(-1))
    return A, b, tag
def solve_exact(M, rhs):
    # M: list of rows (n_eq x n_var) Fractions; returns one solution (free vars = 0) or None
    n = len(M[0]); M = [r[:] + [v] for r, v in zip(M, rhs)]; piv = []; r0 = 0
    for col in range(n):
        p = next((i for i in range(r0, len(M)) if M[i][col] != 0), None)
        if p is None: continue
        M[r0], M[p] = M[p], M[r0]; pv = M[r0][col]; M[r0] = [x / pv for x in M[r0]]
        for i in range(len(M)):
            if i != r0 and M[i][col] != 0:
                f = M[i][col]; M[i] = [x - f * y for x, y in zip(M[i], M[r0])]
        piv.append(col); r0 += 1
    if any(all(x == 0 for x in M[i][:-1]) and M[i][-1] != 0 for i in range(len(M))): return None
    sol = [Fr(0)] * n
    for i, col in enumerate(piv): sol[col] = M[i][-1]
    return sol
step, off = int(sys.argv[1]), int(sys.argv[2]); SHOW = int(sys.argv[3]); c = Counter()
for idx, R0, closers, cls, att in rows[off::step]:
    if not att or any(cls[k] != 'X' for k in att): continue
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E)
    A, b, tag = cell_exact(rs); ok = True
    for k1 in att:
        k = k1 - 1; f = facing(rs, T, k)
        if f is None or f[0] == 0: ok = False; break
        d, xP, xA, side = f; jP, qP = ident(xP, rs); jA, qA = ident(xA, rs)
        if jP is None or jA is None: ok = False; break
        v = [Fr(0)] * 6; rhs = Fr(0); sgn = 1 if side == 'below' else -1
        for j_, q_, s_ in ((jA, qA, sgn), (jP, qP, -sgn)):
            if j_ == 1: rhs -= s_ * q_
            else: v[j_ - 2] += s_ * q_
        A.append(v); b.append(rhs)
    if not ok: c[('skipped: facing ends not identified',)] += 1; continue
    m = len(A); Af = np.array([[float(x) for x in r] for r in A]); bf = np.array([float(x) for x in b])
    res = linprog(bf, A_eq=np.vstack([Af.T, np.ones((1, m))]), b_eq=np.concatenate([np.zeros(6), [1.0]]), bounds=[(0, None)] * m, method='highs')
    if res.status != 0 or res.fun >= -1e-12: c[('float Farkas LP: no ray found (closure may be feasible)', res.status)] += 1; continue
    S = [i for i in range(m) if res.x[i] > 1e-12]
    Meq = [[A[i][q] for i in S] for q in range(6)] + [[Fr(1)] * len(S)]
    y = solve_exact(Meq, [Fr(0)] * 6 + [Fr(1)])
    if y is None or any(v < 0 for v in y):
        c[('exact solve on the support failed', 'none' if y is None else 'negative entry')] += 1; continue
    yA = [sum(y[u] * A[S[u]][q] for u in range(len(S))) for q in range(6)]; yb = sum(y[u] * b[S[u]] for u in range(len(S)))
    good = all(v == 0 for v in yA) and yb < 0
    nesc = sum(1 for i in S if i >= m - len(att))
    c[('EXACT certificate', good, 'escape rows used', nesc, 'of', len(att))] += 1
    cr = [tag[i] for i in S if i < len(tag)]
    ph = tuple(sorted(set('phase 1' if (R is not None and R < 9) else ('phase 2' if R is not None else kd) for R, kd, qs in cr)))
    c[('support: phases and kinds present', ph)] += 1
    c[('support: number of cell rows', len(cr))] += 1
    c[('support: kinds', tuple(sorted(set(kd for R, kd, qs in cr))))] += 1
    if len(cr) <= 2:
        key2 = tuple((None if R is None else ('<9' if R < 9 else '>=9'), kd, qs) for R, kd, qs in cr)
        c[('support with <= 2 cell rows', key2)] += 1
        if c[('support with <= 2 cell rows', key2)] <= SHOW:
            print('CERT | E340 index', idx, '| support', key2, '| attaining', att, '| classes', cls)
            for u, i in enumerate(S):
                lab = tag[i] if i < len(tag) else ('escape row', None, None)
                terms = ' + '.join('(%s) r_%d' % (A[i][q], q + 2) for q in range(6) if A[i][q] != 0)
                print('    y = %s | %s | %s <= %s' % (y[u], lab if i < len(tag) else 'escape row', terms, b[i]))
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
