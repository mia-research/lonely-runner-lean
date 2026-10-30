"""E661: phi-span x_0 |W| and delta-span s |W| of the other block's torus segment over the own window W, for the
gap-strip records with the nearest reading at the own step; min and max of each, separately for landings in W and
after W; and the 186 after-W records by phi-span band. Exact Fractions."""
import math, pickle
from fractions import Fraction as F
from collections import Counter
recs = pickle.load(open('two_block_strip_cascade_v1.pkl', 'rb'))
def sp(p, A, b): return [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
ext = {}; band = Counter()
for (p, b, G, k, t, op, M, mv, R, r) in recs:
    if G <= 0: continue
    v = sp(p, G + p - 1, b)
    ownb = list(range(p)) if k < p else list(range(p, 8)); u = F(1) if k < p else b; s = b if k < p else F(1)
    if min(abs(v[i] - v[k]) for i in range(8) if i != k) < u: continue
    J = max(ownb.index(k), len(ownb) - 1 - ownb.index(k))
    lo, hi = F(1, 8) / u, F(7, 8) / (J * u)
    x0 = min(abs(v[i] - v[k]) for i in range(8) if i not in ownb)
    ph, de = x0 * (hi - lo), s * (hi - lo)
    key = 'in W' if lo <= t <= hi else 'after W'
    e = ext.setdefault(key, [ph, ph, de, de])
    e[0] = min(e[0], ph); e[1] = max(e[1], ph); e[2] = min(e[2], de); e[3] = max(e[3], de)
    if key == 'after W': band[('phi-span < 3/4' if ph < F(3, 4) else 'phi-span in [3/4,1)' if ph < 1 else 'phi-span >= 1')] += 1
for kk, (a, b_, c, d) in ext.items(): print(kk, " phi-span [%s, %s]  delta-span [%s, %s]" % (a, b_, c, d))
print("after-W records by phi-span:", dict(band))
