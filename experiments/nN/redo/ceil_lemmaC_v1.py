# Lemma C check: for a gate crosser every component C of K5 (readings 1..5) on [1,7] lies in Z6 u Z7, meets at most one 6-zone, and has length < 2/rho6 + 4/rho7.
import pickle
from ceil_lib_v1 import *
from ceil_k6_lib_v1 import *
seeds = [norm(list(x)) for x in pickle.load(open('stress_seeds_v1.pkl', 'rb')).keys()] + [norm(X7)]
X24 = [F(t) for t in ['1', '2752864293769/970238379379', '3691147638604/961559468885', '4851775667488/988103849833', '5240560485773/830842598345', '2806730537001/400961505286', '474233610200591258564537783/19451412054102649094869700']]
seeds.append(norm(X24))
viol = 0; worst = None; n = 0; maxc = 0
for x in seeds:
    ok, st, R = crosses(x)
    if not ok: continue
    n += 1
    for a, b in clear_components(x[:5], F(7)):
        # zones of 6 meeting [a,b] (open zone meets closed [a,b])
        m6 = [j for (lo, hi, j) in zones(x[5], F(8)) if lo < b and hi > a]
        L = b - a; bound = 2 / x[5] + 4 / x[6]
        if len(m6) > 1 or not L < bound: viol += 1
        maxc = max(maxc, len(m6))
        sl = bound - L
        if worst is None or sl < worst[0]: worst = (sl, float(L), float(bound))
print('crossers checked', n, 'violations', viol, 'max number of 6-zones meeting a K5 component', maxc, 'smallest slack (bound - length, length, bound)', worst)
# the X24 and X7 numbers
for nm, x in (('X24', norm(X24)), ('X7', norm(X7))):
    c6 = clear_components(x[:6], F(7)); c5 = clear_components(x[:5], F(7))
    print(nm, 'K6 longest', float(max(b-a for a,b in c6)), '-> 2/lmax', float(2/max(b-a for a,b in c6)), 'rho7', float(x[6]), '| K5 comps', [(round(float(a),5), round(float(b),5)) for a,b in c5], 'longest', float(max(b-a for a,b in c5)), '-> 6/lmax5', float(6/max(b-a for a,b in c5)), 'rho6', float(x[5]))
