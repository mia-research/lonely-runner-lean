"""E662: exact maxima of |Delta(N) - Delta(limit)| per N (30Q+r, 120Q+r, 480Q+r) for the six families of
two_block_e558_v1.py; and whether Delta(N) equals Delta(limit) exactly in how many cells per N. Exact Fractions."""
import importlib.util
from fractions import Fraction as F
spec = importlib.util.spec_from_file_location('m', 'two_block_e558_v1.py'); src = open('two_block_e558_v1.py').read().split('for p, b in')[0]
ns = {}; exec(compile(src, 'm', 'exec'), ns); shift = ns['shift']
for p, b in [(2, F(3, 2)), (4, F(3, 2)), (4, F(5, 3)), (6, F(2, 3)), (3, F(7, 4)), (5, F(4, 3))]:
    Q = b.denominator; mx = {30: F(0), 120: F(0), 480: F(0)}; eq = {30: 0, 120: 0, 480: 0}; n = 0
    for r_ in range(Q):
        for j in range(48):
            tau0 = F(j, 48); lim, _ = shift(p, b, 100000 * Q + r_, tau0, False); n += 1
            for m in (30, 120, 480):
                d, _ = shift(p, b, m * Q + r_, tau0, False)
                mx[m] = max(mx[m], abs(d - lim)); eq[m] += (d == lim)
    print("p=%d b=%s cells %d | exact max |Delta(N)-Delta(lim)|: N=30Q: %s  120Q: %s  480Q: %s | cells equal exactly: %d, %d, %d" %
          (p, b, n, mx[30], mx[120], mx[480], eq[30], eq[120], eq[480]))
