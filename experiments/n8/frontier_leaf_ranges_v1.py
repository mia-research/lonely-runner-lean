# E832: per range, the centre ratio rho7/rho5 of the uncertified leaves at D = 64 (exact Fractions), the nearest of the four clusters 21/4, 7, 63/10, 25/4, and the range of rho7 of the centres.
import glob, collections
from fractions import Fraction as F
CL = [F(21, 4), F(7), F(63, 10), F(25, 4)]
for f in sorted(glob.glob('frontier_box_dfs_v1_leaves64_*.txt')):
    cnt = collections.Counter(); r7 = []
    n = 0
    for l in open(f):
        v = [int(x) for x in l.split()]
        if not v: continue
        D, nb = v[0], v[1:]
        c = [F(2 * a + 1, 2 * D) for a in nb]
        ratio = c[5] / c[3]; k = min(CL, key=lambda a: abs(a - ratio))
        cnt[(str(k), abs(k - ratio) < F(1, 40))] += 1; r7.append(c[5]); n += 1
    print(f.split('leaves64_')[1], 'leaves', n, '| nearest cluster (within 1/40?):', sorted(cnt.items()), '| rho7 centre in [%s, %s]' % (min(r7), max(r7)) if r7 else '')
