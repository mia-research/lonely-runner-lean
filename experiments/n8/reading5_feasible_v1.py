"""E950: the 8 cells where reading 5's escape alone was not refuted (reading5_cert_v1 'FEASIBLE?').  Exact verdicts.
Float LP (steers only): the tightened cell plus reading 5's escape row, maximising the escape margin.  Points
member + lam (opt - member), lam from 1 - 10^-9 down, kept if the EXACT cascade gives the member's path; at each, reading 5's
class exactly (crosser_equality_v1's rule) and min_k B_k against 8 end."""
import numpy as np
from scipy.optimize import linprog
src = open('attain_lp_v2.py').read(); exec(src.split("step, off = int(sys.argv[1]), int(sys.argv[2]); c = Counter()\n")[0])
def path_sig(rs):
    T, path = cascade(rs, E); t = E; sig = []
    for s in path:
        lap = floor(s * t + E); t = (lap + E) / s; sig.append((rs.index(s), lap))
    return T, tuple(sig)
def cls5(rs):
    T, path = cascade(rs, E); k = 4; six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]
    ents = [(floor(x * T + E) + 1 - E) / x for x in rs]; end = min(ents)
    ws = windows(six, E, T1); n = next(i for i, (a, b, o) in enumerate(ws) if a <= T <= b); a, b, o = ws[n]
    if b > end: return 'C'
    if b - a >= Fr(1, 4) / lo: return 'L'
    P = [(l, h) for l, h, m in passes(a, b, lo, rs[k + 1])]
    if not P: return 'P'
    A = P
    for jj in range(n):
        if not A: break
        A = passes_in(ws[jj][0], ws[jj][1], A)
    return 'X' if not A else 'N'
for idx in (100073, 101555, 102875, 103255, 100696, 100670, 101195, 101279):
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E); _, sig0 = path_sig(rs)
    d, xP, xA, side = facing(rs, T, 4); jP, qP = ident(xP, rs); jA, qA = ident(xA, rs)
    A, bb = cell(rs); v = np.zeros(6); rhs = 0.0; sgn = 1 if side == 'below' else -1
    for j_, q_, s_ in ((jA, qA, sgn), (jP, qP, -sgn)):
        if j_ == 1: rhs -= s_ * float(q_)
        else: v[j_ - 2] += s_ * float(q_)
    Ab = np.vstack([A, v]); bv = np.concatenate([bb, [rhs]]); bv = bv - 1e-9 * np.linalg.norm(Ab, axis=1)
    res = linprog(v, A_ub=Ab, b_ub=bv, bounds=[(1.0, 10 * float(rs[q])) for q in range(1, 7)], method='highs')
    print('E340', idx, '| side', side, '| P end r_%s x %s, A end r_%s x %s | LP status' % (jP, qP, jA, qA), res.status)
    if res.status != 0: continue
    opt = [Fr(1)] + [Fr(float(x)) for x in res.x]; done = False
    for e in (9, 7, 5, 3, 2, 1):
        lam = 1 - Fr(1, 10 ** e)
        p = [rs[q] + lam * (opt[q] - rs[q]) for q in range(7)]
        if sorted(p) != p or path_sig(p)[1] != sig0: continue
        r = minB_vs_end(p)
        print('   lam 1 - 10^-%d: same path; reading 5 class %s; min B_k > 8 end: %s' % (e, cls5(p), r[0]), flush=True); done = True; break
    if not done: print('   no tried lam keeps the path')
