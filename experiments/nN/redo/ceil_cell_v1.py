import time
from ceil_lib_v1 import *
ok, st, R = crosses(X7)
print('gate crossed', ok, 'landing', R, float(R), 'moves', len(st), 'path', [(s['setter']+1, s['lap']) for s in st])
rows, tags, _ = cell_rows(X7)
print('rows', len(rows), 'feasible at arrangement', feasible_exact(rows, norm(X7)))
for idx in (7, 6):
    r = maxrho(rows, idx)
    if r is None: print('max rho%d: LP basis not verified' % idx); continue
    X, lam = r
    print('max rho%d over closed fine cell = %s = %.12f' % (idx, X[idx-1], float(X[idx-1])))
    print(' vertex', [str(t) for t in X]); print(' feasible exactly', feasible_exact(rows, X), ' dual rows', {i: str(l) for i, l in lam.items()})
    T = dedupe_rows(rows, tight(rows, X)); print(' tight distinct rows', len(T))
    for i in T: print('  ', rows[i], row_meaning(tags[i]))
    # Farkas certificate: sum lam_i a_i[1:] = -e_idx  and sum lam_i a_i[0] -> bound
    tot = [sum(lam[i]*rows[i][k] for i in lam) for k in range(7)]
    print(' certificate: sum lam*a =', [str(t) for t in tot], '(coordinate 0 = constant; need = -e_idx on 1..6, so rho_%d <= const)' % idx)
    pa, R2 = path(norm(X)); print(' path at vertex (closure point) landing', R2)
