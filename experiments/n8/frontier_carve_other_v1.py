# E826: the violators whose first exact uncovered point is not 73/r7: which zone ends there, how wide the gap is, relative to the grid step 1/4000.
import pickle, collections
from fractions import Fraction as F
vs = pickle.load(open('frontier_carve_viol_v1.pkl', 'rb'))
def zones(rs):
    iv = []
    for idx, r in enumerate(rs):
        r = F(r)
        for j in range(1, int(7 * r / 8) + 3):
            a, b = F(8 * j - 1) / r, F(8 * j + 1) / r
            if b > 1 and a < 7: iv.append((a, b, idx + 2, j))
    return iv
rows = []
for v in vs:
    iv = zones(v)
    cur = max(b for a, b, i, j in iv if a < 1)
    while cur <= 7:
        nxt = [b for a, b, i, j in iv if a < cur and b > cur]
        if not nxt: break
        cur = max(nxt)
    g = cur
    if g == F(73) / F(v[5]): continue
    ender = [(i, j) for a, b, i, j in iv if b == g][0]
    nxt_start = min(a for a, b, i, j in iv if a > g)
    rows.append((v, g, ender, nxt_start - g))
print('violators with the first gap not at 73/r7:', len(rows))
print('zone that ends at the gap (reading index, lap):', collections.Counter(r[2] for r in rows).most_common(8))
w = sorted(r[3] for r in rows)
print('gap width: min', w[0], 'max', w[-1], '; all below the grid step 1/4000:', all(x < F(1, 4000) for x in w))
print('gap location: min', float(min(r[1] for r in rows)), 'max', float(max(r[1] for r in rows)))
