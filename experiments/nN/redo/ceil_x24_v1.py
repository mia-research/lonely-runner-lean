# exact arrangement with rho_7 ~ 24.38 (found by ceil_climb_v1.py, verified in ceil_verify24_v1.py): independent exact checks, its fine cell, exact max rho_7 / rho_6
import sys
from ceil_lib_v1 import *
from ceil_k6_lib_v1 import *
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
X24 = [F(t) for t in ['1', '2752864293769/970238379379', '3691147638604/961559468885', '4851775667488/988103849833', '5240560485773/830842598345', '2806730537001/400961505286', '474233610200591258564537783/19451412054102649094869700']]
x = norm(X24); print('readings', [float(t) for t in x], 'increasing', all(x[i] < x[i+1] for i in range(6)))
st, R = path(x); print('path() landing', R, float(R), 'moves', len(st), [(s['setter']+1, s['lap']) for s in st])
o = outcome(x); print('outcome opener', o['opener'], 'closer', o['closer'], 'width', float(o['width']), 'nmoves', o['nmoves'])
print('independent: clear components of all 7 readings on [1,7]:', clear_components(x, F(7)))
print('K6 components on [1,7]:', [(float(a), float(b), in_zone7(x[6], a, b)) for a, b in clear_components(x[:6], F(7))])
print('states', [str(s['R']) for s in st][:3], '... state 9 present:', any(s['R2'] == 9 or s['R'] == 9 for s in st))
rows, tags, _ = cell_rows(x); print('rows', len(rows), 'x feasible', feasible_exact(rows, x))
for idx in (7, 6):
    r = maxrho(rows, idx)
    if not r: print('max rho%d: basis not verified' % idx); continue
    X, lam = r; print('max rho%d over closed fine cell = %s = %.9f' % (idx, X[idx-1], float(X[idx-1])), 'vertex', [str(t) for t in X], 'exact feasible', feasible_exact(rows, X))
    for i in dedupe_rows(rows, tight(rows, X)): print('   tight', rows[i], row_meaning(tags[i]), ' dual', lam.get(i))
