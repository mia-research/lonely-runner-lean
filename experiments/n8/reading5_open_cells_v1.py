"""E950: the 6 cells of reading5_feasible_v1 where the built point kept reading 5 class X or made it the closer (2026-11-25).
More points per cell: the float LP (steers only) on the tightened cell plus reading 5's escape row, with 12 objectives
(+-e_i, and the escape margin); points member + lam (vertex - member), lam = 1 - 10^-e (e = 9, 6, 3) and 1/2, kept if the EXACT
cascade gives the member's path; at each, reading 5's class exactly."""
exec(open('reading5_feasible_v1.py').read().split("for idx in (100073")[0])
from collections import Counter
for idx in (100073, 101555, 103255, 100696, 100670, 101279):
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E); _, sig0 = path_sig(rs)
    d, xP, xA, side = facing(rs, T, 4); jP, qP = ident(xP, rs); jA, qA = ident(xA, rs)
    A, bb = cell(rs); v = np.zeros(6); rhs = 0.0; sgn = 1 if side == 'below' else -1
    for j_, q_, s_ in ((jA, qA, sgn), (jP, qP, -sgn)):
        if j_ == 1: rhs -= s_ * float(q_)
        else: v[j_ - 2] += s_ * float(q_)
    Ab = np.vstack([A, v]); bv = np.concatenate([bb, [rhs]]); bv = bv - 1e-9 * np.linalg.norm(Ab, axis=1)
    objs = [v] + [s * np.eye(6)[i] for i in range(6) for s in (1, -1)]
    c = Counter()
    for ob in objs:
        res = linprog(ob, A_ub=Ab, b_ub=bv, bounds=[(1.0, 10 * float(rs[q])) for q in range(1, 7)], method='highs')
        if res.status != 0: c['LP not solved'] += 1; continue
        opt = [Fr(1)] + [Fr(float(x)) for x in res.x]
        for lam in (1 - Fr(1, 10 ** 9), 1 - Fr(1, 10 ** 6), 1 - Fr(1, 10 ** 3), Fr(1, 2)):
            p = [rs[q] + lam * (opt[q] - rs[q]) for q in range(7)]
            if sorted(p) != p or path_sig(p)[1] != sig0: c['path changed'] += 1; continue
            c['reading 5 ' + cls5(p)] += 1
    print('E340', idx, dict(c), flush=True)
