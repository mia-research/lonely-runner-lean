# E827: for each exact carve of [1,7] found by the annealer, the first lonely R >= 1 of the seven readings (1, r2..r7): zones (8j-1, 8j+1)/r, open, so a boundary point is lonely.  Exact Fractions of the float readings.
import re, glob
from fractions import Fraction as F
def first_lonely(rs, Rmax=60):
    iv = []
    for r in rs:
        r = F(r); j = 1
        while F(8 * j - 1) / r < Rmax:
            iv.append((F(8 * j - 1) / r, F(8 * j + 1) / r)); j += 1
    iv.sort(); cur = F(1)
    # smallest R >= 1 not in any open interval
    changed = True
    while changed:
        changed = False
        for a, b in iv:
            if a < cur < b: cur = b; changed = True
    return cur
cands = []
for f in sorted(glob.glob('frontier_seam_anneal_v1_s*.out')):
    for l in open(f):
        if l.startswith('[') and l.count(',') == 5: cands.append((f, [float(x) for x in l.strip('[]\n ').split(',')]))
for f, v in cands:
    R = first_lonely([1.0] + v)
    print(f[-6:-4], 'rho7 =', float(v[5]), '| first lonely R =', float(R), '| in W_0 [1,7]:', R <= 7, '| in W_1 [9,15]:', 9 <= R <= 15, '| below 17:', R < 17, '| exact R =', R)
