# E826: for each of the 1,014 grid violators, the first uncovered R (exact) against the seam interval (73/r7, 31/r6).
import pickle
from fractions import Fraction as F
vs = pickle.load(open('frontier_carve_viol_v1.pkl', 'rb'))
def first_gap(rs):
    iv = []
    for r in rs:
        r = F(r)
        for j in range(1, int(7 * r / 8) + 3):
            a, b = F(8 * j - 1) / r, F(8 * j + 1) / r
            if b > 1 and a < 7: iv.append((a, b))
    if not any(a < 1 < b for a, b in iv): return F(1)
    cur = max(b for a, b in iv if a < 1)
    while cur <= 7:
        nxt = [b for a, b in iv if a < cur and b > cur]
        if not nxt: return cur
        cur = max(nxt)
    return None
n = 0; eq = 0; inside = 0; widths = []
for v in vs:
    g = first_gap(v)
    if g is None: continue
    n += 1
    lo = F(73) / F(v[5]); hi = F(31) / F(v[4])
    if g == lo: eq += 1
    if lo <= g < hi: inside += 1
    widths.append(hi - lo)
print('violators', len(vs), 'with an exact uncovered point:', n, '; first uncovered point equal to 73/r7 (exit of the lap-9 zone of r7):', eq, '; first uncovered point in [73/r7, 31/r6):', inside)
print('seam interval width 31/r6 - 73/r7 over all 1014: min', min(widths), 'max', max(widths), '; all below the grid step 1/4000:', all(w < F(1, 4000) for w in widths))
