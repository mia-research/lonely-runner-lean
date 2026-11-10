# E833: (1) for the leaves that a window type certified at D = 64 (clusters 21/4, 7, 63/10, 25/4): the common interval of the certifying type's window over the 64 corners, [max X, min Y] (exact): width < 0 means no common R0, which is why the fixed-R0 test failed while the window type holds;  (2) for the 35,265 uncertified leaves of the window-type run without planes in [35,37) (D = 256): whether h1 = rho7 - 7 rho5 or h2 = 3 rho6 - 5 rho4 takes both signs on the box corners (exact).
import sys, collections, glob
from fractions import Fraction as F
sys.argv = ['x']
PLANES = [(0, 0, 0, -7, 0, 1), (0, 0, -5, 0, 3, 0)]
def hval(h, u): return sum(F(c) * x for c, x in zip(h, u))
exec(open('frontier_window_cert_v1.py').read().split("def work(item):")[0])
def cert_type(D, n):
    V = corners(D, n); tried = set()
    for u in [tuple(F(2 * n[i] + 1, 2 * D) for i in range(6)), V[0], V[63], V[21], V[42]]:
        for X, Y, xv, yv in windows(u):
            ineqs = wtype(u, X, Y, xv); k = tuple(ineqs)
            if k in tried: continue
            tried.add(k)
            if holds(ineqs, V): return X, Y, V
    return None
def val(desc, u):
    A, s = desc
    return F(A) / u[s] if s is not None else F(A)
cnt = collections.Counter(); widths = []
for f in sorted(glob.glob('frontier_box_dfs_v1_leaves64_*_*.txt')):
    if 'wleaves' in f or 'pleaves' in f: continue
    for l in open(f):
        v = [int(x) for x in l.split()]
        if not v: continue
        D, n = v[0], tuple(v[1:])
        r = cert_type(D, n)
        if r is None: cnt['not certified by one window type'] += 1; continue
        X, Y, V = r
        lo = max(val(X, u) for u in V); hi = min(val(Y, u) for u in V)
        cnt['window type holds; common interval over the corners empty' if hi < lo else 'window type holds; common interval nonempty'] += 1
        widths.append(hi - lo)
print('(1) leaves at D = 64 by the outcome of one window type:', sorted(cnt.items()))
print('    among those with a window type: largest (min Y - max X) =', max(widths), '; smallest =', min(widths))
n = 0; both = 0; neither = 0
for l in open('frontier_box_dfs_v1_leaves64_35_37_wleaves_256.txt'):
    v = [int(x) for x in l.split()]
    if not v: continue
    D, nb = v[0], tuple(v[1:]); V = corners(D, nb); n += 1
    s1 = [hval(PLANES[0], u) for u in V]; s2 = [hval(PLANES[1], u) for u in V]
    if (min(s1) < 0 < max(s1)) or (min(s2) < 0 < max(s2)): both += 1
    else: neither += 1
print('(2) uncertified leaves of the window-type run in [35,37) at D = 256:', n, '| h1 or h2 takes both signs on the corners:', both, '| neither does:', neither)
