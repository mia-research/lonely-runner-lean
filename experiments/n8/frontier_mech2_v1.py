# E833: for 25 random leaves per range (seed 2) that no single window type certifies at D = 64, the 64 children at D = 128: for each child certified by a window type, the common interval [max X, min Y] of the window over the 64 corners (exact): empty, a single point, or of positive width (a positive width means a fixed R0 would certify the child).
import sys, collections, random
from fractions import Fraction as F
sys.argv = ['x']
exec(open('frontier_mech_v1.py').read().split("cnt = collections.Counter()")[0])
exec(open('frontier_plane_cert_v1.py').read().split("def sorted_feasible")[0].split("exec(open('frontier_window_cert_v1.py')")[0] + open('frontier_plane_cert_v1.py').read().split("PLANES = [(0, 0, 0, -7, 0, 1), (0, 0, -5, 0, 3, 0)]")[1].split("def sorted_feasible")[0])
random.seed(2)
res = collections.defaultdict(collections.Counter)
for rng in ('29_31', '35_37', '39_41'):
    L = []
    for l in open('frontier_box_dfs_v1_leaves64_%s.txt' % rng):
        v = [int(x) for x in l.split()]
        if v: L.append((v[0], tuple(v[1:])))
    random.shuffle(L); tested = 0
    for D, n in L:
        if cert_type(D, n) is not None: continue
        if tested >= 25: break
        tested += 1
        for m in range(64):
            c = tuple(2 * n[i] + ((m >> i) & 1) for i in range(6))
            if not sorted_feasible(c): continue
            r = cert_type(2 * D, c)
            if r is None:
                V = corners(2 * D, c)
                strad = any(min(hval(h, u) for u in V) < 0 < max(hval(h, u) for u in V) for h in PLANES)
                res[rng]['no single type; straddles h1 or h2: %s; plane-split certifies: %s' % (strad, cert_poly(V, PLANES))] += 1; continue
            X, Y, V = r
            lo = max(val(X, u) for u in V); hi = min(val(Y, u) for u in V)
            res[rng]['empty' if hi < lo else ('single point' if hi == lo else 'positive width')] += 1
for k, v in res.items(): print(k, '| children at D=128 of 25 leaves each:', dict(v))
