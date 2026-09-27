"""E128: in late band shapes (copy 0 = [1,7] fully covered), where is copy 1's first uncovered point, relative to the
top's gaps G_2 = [105/s7, 15] and G'_2 = the top's other copy-1 gap, and to the images of copy-0's last clear point?
Many late shapes by walking the late region.  Exact."""
import random, sys
from fractions import Fraction as F
from collections import Counter
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
D1 = 27720; rnd = random.Random(31)
SEEDS = [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302),
         (1, 3.15, 4.2099, 4.7242, 5.225, 5.7897, 7.4429)]
c = Counter(); n = 0
for sd in SEEDS:
    T = [int(round(x * D1)) for x in sd]
    for step in range(2500):
        L = list(T); i = rnd.randrange(1, 7); L[i] += rnd.randrange(-500, 501)
        U = sorted(set(L))
        if len(U) < 7 or U[0] != D1 or not (7 * D1 < U[-1] < 9 * D1): continue
        s = [F(d, D1) for d in U]
        if clear_set(s, F(1), F(7)): continue          # copy 0 not covered: not late
        T = U
        if step % 10: continue
        S = s[-1]; C1 = clear_set(s, F(9), F(15)); n += 1
        first = C1[0][0]
        inG2 = any(a <= 15 and b >= F(105) / S for a, b in C1)          # some clear point of copy 1 in G_2
        c['copy 1 meets G2 = [105/s7, 15]' if inG2 else 'copy 1 misses G2'] += 1
        c['first clear point of copy 1 in G2' if first >= F(105) / S else 'first clear point before G2'] += 1
        c['R = 9 clear' if first == 9 else 'R = 9 blocked'] += 1
print("late shapes (copy 0 covered):", n)
for k, v in sorted(c.items()): print("   %5d  %s" % (v, k))
