# exact max of rho_IDX over the fine cell of each seed (distinct fine cells), seeds ordered by rho_IDX descending; time-limited.
import sys, time, pickle
from ceil_lib_v1 import *
IDX = int(sys.argv[1]); LIM = float(sys.argv[2]); T0 = time.time()
seeds = list(pickle.load(open('stress_seeds_v1.pkl', 'rb')).keys())
seeds.sort(key=lambda x: -x[IDX-1]/x[0])
seen = {}; done = 0; fail = 0
for x in seeds:
    if time.time() - T0 > LIM: break
    x = norm(list(x)); ok, st, R = crosses(x)
    if not ok: continue
    rows, tags, _ = cell_rows(x); sig = sigkey(tags, st)
    if sig in seen: continue
    done += 1
    r = maxrho(rows, IDX)
    if r is None: fail += 1; seen[sig] = None; continue
    X, lam = r; seen[sig] = (X[IDX-1], x, X, lam, tags, rows)
print('seeds', len(seeds), 'distinct fine cells processed', done, 'lp unverified', fail, 'time', round(time.time()-T0))
vals = sorted([v for v in seen.values() if v], key=lambda v: -v[0])
print('top exact cell maxima of rho%d:' % IDX, [(str(v[0]), round(float(v[0]), 6)) for v in vals[:10]])
v = vals[0]; print('best vertex', [str(t) for t in v[2]])
for i in dedupe_rows(v[5], tight(v[5], v[2])): print('  ', v[5][i], row_meaning(v[4][i]))
print('best member of that cell', [str(t) for t in v[1]])
print('smallest rho_%d-max among the cells (not a bound)' % IDX, str(vals[-1][0]), float(vals[-1][0]))
pickle.dump([(str(a[0]), [str(t) for t in a[1]], [str(t) for t in a[2]]) for a in vals[:50]], open('ceil_multistart%d_v1.pkl' % IDX, 'wb'))
