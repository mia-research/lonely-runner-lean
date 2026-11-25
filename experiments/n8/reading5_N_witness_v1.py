"""E950: the two exact arrangements, in the path cells of E340 102875 and 101195, where reading 5 is class N."""
exec(open('reading5_feasible_v1.py').read().split("for idx in (100073")[0])
for idx in (102875, 101195):
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E); _, sig0 = path_sig(rs)
    d, xP, xA, side = facing(rs, T, 4); jP, qP = ident(xP, rs); jA, qA = ident(xA, rs)
    A, bb = cell(rs); v = np.zeros(6); rhs = 0.0; sgn = 1 if side == 'below' else -1
    for j_, q_, s_ in ((jA, qA, sgn), (jP, qP, -sgn)):
        if j_ == 1: rhs -= s_ * float(q_)
        else: v[j_ - 2] += s_ * float(q_)
    Ab = np.vstack([A, v]); bv = np.concatenate([bb, [rhs]]); bv = bv - 1e-9 * np.linalg.norm(Ab, axis=1)
    res = linprog(v, A_ub=Ab, b_ub=bv, bounds=[(1.0, 10 * float(rs[q])) for q in range(1, 7)], method='highs')
    opt = [Fr(1)] + [Fr(float(x)) for x in res.x]; lam = 1 - Fr(1, 10 ** 9)
    p = [rs[q] + lam * (opt[q] - rs[q]) for q in range(7)]
    Tp, _ = cascade(p, E)
    print('cell of E340', idx, '| same path', path_sig(p)[1] == sig0, '| reading 5 class', cls5(p), '| R*', 8 * Tp, '| min B_k = 8 end', not minB_vs_end(p)[0])
    print('   readings', [str(x) for x in p])
    print('   readings (floats, steer only)', [round(float(x), 9) for x in p], '| member (floats)', [round(float(x), 9) for x in rs])
