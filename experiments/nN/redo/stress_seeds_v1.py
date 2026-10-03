# stress_seeds_v1.py -- collect exact gate-crossing arrangements (exact landing > 9) from stored exact members (J1, J2) and
# rationalised J3 witnesses (each re-checked with the exact cascade).  Writes stress_seeds_v1.pkl; prints counts only.
import sys, pickle; sys.path.insert(0, '.')
exec(open('stress_lib_v1.py').read())
T0 = time.time(); seeds = {}
def add(rs, src):
    rs = sorted(rs)
    if rs[0] != 1 or len(set(rs)) != 7: return
    rh = [Q(x) for x in rs]; steps, R = fpath(rh)
    if R > 9: seeds[tuple(rs)] = (src, float(R), len(steps))
for f in ('cell_members7_J1.pkl', 'cell_members_J2.pkl'):
    d = pickle.load(open(f, 'rb')); n = 0
    for it in d:
        add([F(x) for x in it[1]], f); n += 1
    print(f, n, 'seeds so far', len(seeds), round(time.time() - T0)); del d
d = pickle.load(open('terminals5_J3.pkl', 'rb')); print('J3 loaded', len(d), round(time.time() - T0))
n = 0
for it in d:
    w = it[-1]
    for den in (10**6, 10**9):
        rs = [F(1)] + [F(float(x)).limit_denominator(den) for x in w]
        add(rs, 'J3w%d' % den)
    n += 1
    if time.time() - T0 > 480: print('stopped at', n); break
print('J3 processed', n, 'seeds', len(seeds), round(time.time() - T0))
pickle.dump(seeds, open('stress_seeds_v1.pkl', 'wb'))
from collections import Counter
c = Counter(); mx = max(seeds.values(), key=lambda t: t[1]); print('max landing among seeds', mx)
for rs, (src, R, ns) in seeds.items(): c[(src, int(R))] += 1
print(sorted(c.items()))
print('rho_7 max among seeds', float(max(r[6] for r in seeds)), 'rho_6 max', float(max(r[5] for r in seeds)))
