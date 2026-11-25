"""free_escape_v1 (E952 rule 22): for each two-reading class-X attaining reading that the closed cell does NOT block (cycle_read_v1:
697), a float LP (STEERS ONLY) over the tightened path cell (short_window_cell_lp_v2.cell) pushes r_jA - thr r_jP past 0 the escaping
way; exact points p = member + lam (opt - member), lam in 1 - 10^-6, 1 - 10^-3, 9/10, 1/2, kept if the EXACT cascade gives the member's
path.  At each kept point, exactly: has r_jA/r_jP crossed thr; do the two window ends keep their zone-edge identities; and does the
reading escape (its P and A overlap: one_mover_bound_v1.inter non-empty)?  First kept point per reading that crosses.
Base: cycle_read_v1.  E952: the 625 cycle crossers (E951 item 3) read in times.  Exact Fractions.
Pass formula (E930 item 1; PROVISIONAL: covering): the moved reading x blocks a window [a, b] at lap m iff
(8m-1)/(8a) < x < (8m+1)/(8b).  Below side: x_P = (8m_P+1)/(8 b_n) (upper end at W_k's end b_n), x_A = (8m_A-1)/(8 a_j)
(lower end at an earlier window's start a_j); x can block both iff x_A < x_P iff b_n / a_j < (8m_P+1)/(8m_A-1).  Above side
mirrored: x_P = (8m_P-1)/(8 a_n), x_A = (8m_A+1)/(8 b_j); both iff a_n / b_j > (8m_P-1)/(8m_A+1).
For every attaining reading of the 2,607 with single identifications: provenance of x_P and x_A (pin_form_v2), the readings
whose zone edges give the two window times (8 r t = 8u -+ 1), and checks: (a) x_P, x_A equal the formula; (b) the time-ratio
inequality fails at the member (class X); (c) pin (same reading) vs two readings; for two readings: the time ratio as
(8u-+1)/(8w+-1) * r_j / r_i, and whether the ratio graph of the closed cell (cert_cycle_v2) bounds r_j / r_i on the wrong side
of the needed value (blocked), and by how many cell rows."""
import sys
from fractions import Fraction as Fr
from collections import Counter
import numpy as np
from scipy.optimize import linprog
src = open('pin_form_v2.py').read(); exec(src.split("step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()\n")[0])
src4 = open('attain_lp_cert_v4.py').read(); exec('def cell_exact' + src4.split('def cell_exact')[1].split('def solve_exact')[0])
src2 = open('cert_cycle_v2.py').read(); exec('def to_edges' + src2.split('def to_edges')[1].split('step, off = int')[0])
def fw(E_):
    U = [[None] * 7 for _ in range(7)]
    for i in range(7): U[i][i] = Fr(1)
    for (i, j), (w, tg) in E_.items():
        if U[i][j] is None or w < U[i][j]: U[i][j] = w
    for m in range(7):
        for i in range(7):
            if U[i][m] is None: continue
            for j in range(7):
                if U[m][j] is None: continue
                v = U[i][m] * U[m][j]
                if U[i][j] is None or v < U[i][j]: U[i][j] = v
    return U
step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()
for idx, R0, closers, cls, att in rows[off::step]:
    if not att or any(cls[k] != 'X' for k in att): continue
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E); o = rs.index(path[-1]) + 1
    bad = False
    for k1 in att:
        f = facing(rs, T, k1 - 1)
        if f is None or f[0] == 0 or ident(f[1], rs)[0] is None or ident(f[2], rs)[0] is None: bad = True
    if bad: continue
    U = None
    for k1 in att:
        d, xP, xA, side = facing(rs, T, k1 - 1); IP, IA = idents(xP, rs), idents(xA, rs)
        if not (len(IP) == 1 and len(IA) == 1): c[('reading', 'several identifications')] += 1; continue
        k = k1 - 1; six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]
        ws = windows(six, E, T1); n = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y); a, b = ws[n][0], ws[n][1]
        hi = rs[k + 1] if k < 6 else ((a + b) / (b - a) + 1) / (8 * b) + 1
        P = prov_passes(a, b, lo, hi, 'clip lo', 'clip hi', n)
        A = [(lo, hi, 'clip lo', 'clip hi')]
        for jj in range(n):
            nA = []
            for l, h, lt, ht in A: nA.extend(prov_passes(ws[jj][0], ws[jj][1], l, h, lt, ht, jj))
            A = nA
        pP = next((lt if l == xP else ht) for l, h, lt, ht in P if xP in (l, h))
        pA = next((lt if l == xA else ht) for l, h, lt, ht in A if xA in (l, h))
        if pP[0] != 'win' or pA[0] != 'win': c[('reading', 'an end is a clip', pP[0], pA[0])] += 1; continue
        tP = ws[pP[1]][0] if pP[2] == 'lower' else ws[pP[1]][1]; tA = ws[pA[1]][0] if pA[2] == 'lower' else ws[pA[1]][1]
        mP, mA = pP[3], pA[3]
        fP = Fr(8 * mP + 1, 8) / tP if pP[2] == 'upper' else Fr(8 * mP - 1, 8) / tP
        fA = Fr(8 * mA + 1, 8) / tA if pA[2] == 'upper' else Fr(8 * mA - 1, 8) / tA
        if side == 'below':
            okf = (pP[2], pA[2]) == ('upper', 'lower'); need = Fr(8 * mP + 1, 8 * mA - 1); ratio = tP / tA; block = ratio >= need
        else:
            okf = (pP[2], pA[2]) == ('lower', 'upper'); need = Fr(8 * mP - 1, 8 * mA + 1); ratio = tP / tA; block = ratio <= need
        c[('reading', side, 'ends as formula', okf and fP == xP and fA == xA, 'time-ratio inequality fails at member (blocked)', block)] += 1
        jP, jA = IP[0][0], IA[0][0]
        if jP == jA: c[('reading', 'pin (one reading)')] += 1; continue
        # two readings: window times tP = gP / r_jP, tA = gA / r_jA with g = (8u -+ 1)/8
        gP, gA = tP * rs[jP - 1], tA * rs[jA - 1]
        okg = (8 * gP).denominator == 1 and (8 * gA).denominator == 1
        c[('reading', 'two readings', 'window times are zone edges of jP and jA', okg)] += 1
        # ratio = (gP/gA) * r_jA / r_jP ; blocked needs r_jA / r_jP on one side of need * gA / gP
        thr = need * gA / gP
        if U is None:
            A_, b_, tag_ = cell_exact(rs); U = fw(to_edges(A_, b_, tag_, Counter(), 'x'))
        # U[i][j] = least upper bound on r_i / r_j over the closed cell (from the ratio graph)
        iA, iP = jA - 1, jP - 1
        def path_sig(rs_):
            T_, path_ = cascade(rs_, E); t = E; sig = []
            for s_ in path_:
                lap = floor(s_ * t + E); t = (lap + E) / s_; sig.append((rs_.index(s_), lap))
            return tuple(sig)
        def try_escape(sgn):
            Am, bm = cell(rs); bm = bm - 1e-9 * np.linalg.norm(Am, axis=1)
            obj = np.zeros(6)
            for jj_, cf in ((iA, 1.0), (iP, -float(thr))):
                if jj_ > 0: obj[jj_ - 1] += sgn * cf
            const = sum(sgn * cf for jj_, cf in ((iA, 1.0), (iP, -float(thr))) if jj_ == 0)
            res = linprog(obj, A_ub=Am, b_ub=bm, bounds=[(1.0, 10 * float(rs[q])) for q in range(1, 7)], method='highs')
            if res.status != 0: return ('LP status', res.status)
            opt = [Fr(1)] + [Fr(float(v)) for v in res.x]; sig0 = path_sig(rs)
            for lam in (1 - Fr(1, 10 ** 6), 1 - Fr(1, 10 ** 3), Fr(9, 10), Fr(1, 2)):
                p = [rs[q] + lam * (opt[q] - rs[q]) for q in range(7)]
                if sorted(p) != p or path_sig(p) != sig0: continue
                rat = p[iA] / p[iP]; crossed = (rat < thr) if side == 'below' else (rat > thr)
                if not crossed: continue
                Tp, _ = cascade(p, E); six_ = p[:k] + p[k + 1:]; ws_ = windows(six_, E, T1)
                n_ = next(i for i, (x, y, z) in enumerate(ws_) if x <= Tp <= y)
                tP_ = ws_[pP[1]][0] if pP[2] == 'lower' else ws_[pP[1]][1]; tA_ = ws_[pA[1]][0] if pA[2] == 'lower' else ws_[pA[1]][1]
                keep = pP[1] <= n_ and tP_ * p[jP - 1] == gP and tA_ * p[jA - 1] == gA and n_ == n
                a_, b_ = ws_[n_][0], ws_[n_][1]; lo_ = p[k - 1]
                hi_ = p[k + 1] if k < 6 else ((a_ + b_) / (b_ - a_) + 1) / (8 * b_) + 1
                P_ = [(l, h) for l, h, m in passes(a_, b_, lo_, hi_)]; A2 = [(lo_, hi_)]
                for jj in range(n_):
                    if not A2: break
                    A2 = passes_in(ws_[jj][0], ws_[jj][1], A2)
                return ('crossed at a same-path point', 'window ends kept', keep, 'reading escapes (P meets A)', bool(P_ and A2 and inter(P_, A2)))
            return ('no same-path point crosses at the tried lam',)
        if side == 'below':   # blocked iff r_jA/r_jP >= thr everywhere in cell: lower bound on r_jA/r_jP = 1/U[iP][iA]
            lb = None if U[iP][iA] is None else 1 / U[iP][iA]; cellblock = lb is not None and lb >= thr
            c[('reading', 'two readings', 'below', 'cell lower bound on r_jA/r_jP >= threshold', cellblock)] += 1
            if not cellblock: c[('free reading', 'below') + try_escape(1)] += 1
        else:
            ub = U[iA][iP]; cellblock = ub is not None and ub <= thr
            c[('reading', 'two readings', 'above', 'cell upper bound on r_jA/r_jP <= threshold', cellblock)] += 1
            if not cellblock: c[('free reading', 'above') + try_escape(-1)] += 1
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
