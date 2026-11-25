"""E952: the 625 cycle crossers (E951 item 3) read in times.  Exact Fractions.
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
        if side == 'below':   # blocked iff r_jA/r_jP >= thr everywhere in cell: lower bound on r_jA/r_jP = 1/U[iP][iA]
            lb = None if U[iP][iA] is None else 1 / U[iP][iA]; cellblock = lb is not None and lb >= thr
            c[('reading', 'two readings', 'below', 'cell lower bound on r_jA/r_jP >= threshold', cellblock)] += 1
        else:
            ub = U[iA][iP]; cellblock = ub is not None and ub <= thr
            c[('reading', 'two readings', 'above', 'cell upper bound on r_jA/r_jP <= threshold', cellblock)] += 1
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
