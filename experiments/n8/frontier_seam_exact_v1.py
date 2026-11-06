# E827: exact (Fractions of the float readings) carve test of [1,7] for the annealing candidates, and the seam margin.
import re, glob
from fractions import Fraction as F
def carves(rs):
    iv = []
    for r in rs:
        r = F(r)
        for j in range(1, int(7 * r / 8) + 3):
            a, b = F(8 * j - 1) / r, F(8 * j + 1) / r
            if b > 1 and a < 7: iv.append((a, b))
    if not any(a < 1 < b for a, b in iv): return False, 'R=1 uncovered'
    cur = max(b for a, b in iv if a < 1)
    while cur <= 7:
        nxt = [b for a, b in iv if a < cur and b > cur]
        if not nxt: return False, 'gap at R=%.9f' % float(cur)
        cur = max(nxt)
    return True, ''
cands = []
for f in sorted(glob.glob('frontier_seam_anneal_v1_s*.out')):
    for l in open(f):
        if l.startswith('[') and l.count(',') == 5: cands.append((f, [float(x) for x in l.strip('[]\n ').split(',')]))
print('candidates', len(cands))
for f, v in cands:
    ok, why = carves(v)
    m = F(31) / F(v[4]) - F(73) / F(v[5])
    print(f[-6:-4], 'exact carve:', ok, why, '| rho6 < 7:', F(v[4]) < 7, '| rho7 > 511/31:', F(v[5]) > F(511, 31), '| 31/r6 - 73/r7 > 0:', m > 0, '| rho7 =', float(v[5]))
