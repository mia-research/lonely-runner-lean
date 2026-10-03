# tie_first_v1.py -- zero-width landings (first window a single point) among tree members, exact.
# usage: tie_first_v1.py DATASET [start end]   DATASET in J1, J2
import sys, pickle, time
from fractions import Fraction as F
from collections import Counter
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
ds = sys.argv[1]; s = int(sys.argv[2]) if len(sys.argv) > 2 else 0; e = int(sys.argv[3]) if len(sys.argv) > 3 else 10**9
M = pickle.load(open('cell_members7_%s.pkl' % ds, 'rb'))[s:e]
rows = []; t0 = time.time(); cnt = Counter()
for idx, rh in M:
    steps, R = path(rh)
    ps = [(R * r) % 8 for r in rh]
    assert all(1 <= p <= 7 for p in ps)
    cnt['n'] += 1
    # closer p: width = min over y of (7-p_y)/rho_y  (positions at R*; entries of next lap) -- zero iff some p_y == 7
    if 7 not in ps: continue
    en = [(i + 1, int((R * r + 1) / 8)) for i, (r, p) in enumerate(zip(rh, ps)) if p == 7]
    ex = [(i + 1, int((R * r - 1) / 8)) for i, (r, p) in enumerate(zip(rh, ps)) if p == 1]
    op = (steps[-1]['setter'] + 1, steps[-1]['lap']) if steps else None
    rows.append(dict(idx=idx, rh=rh, R=R, nm=len(steps), opener=op, exits=ex, entries=en, ps=ps))
pickle.dump(rows, open('tie_first_%s_%d_v1.pkl' % (ds, s), 'wb'))
print(ds, s, e, 'members', cnt['n'], 'zero-width', len(rows), 'sec', round(time.time() - t0))
