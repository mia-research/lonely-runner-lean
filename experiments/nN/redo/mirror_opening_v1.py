"""The mirror opening, checked exactly.  At a simple pinch t0 of whole-number readings (one runner leaving at +1/8, one
entering at -1/8, the rest strictly clear), the mirror 1 - t0 is the same two runners with roles swapped.  Claim: along
a line of readings d + s*D crossing the pinch wall, t0 opens on one side and 1 - t0 on the other.
Test: the 6 fragile sets of pinch_types_v1, each simple pinch, 200 random integer directions D (fixed seed), s = +-eps:
is there a lonely interval within 1/100 of t0, of 1 - t0?  Exact (Fraction), BSM."""
import random
from fractions import Fraction as F
from math import floor, ceil
from collections import Counter
from pinch_types_v1 import edges, pos, E8

def lonely_near(R, c, w):
    """does the clear set of readings R contain an interval of positive length inside [c - w, c + w]?"""
    lo, hi = c - w, c + w
    zones = []
    for d in R:
        for k in range(floor(d * lo) - 1, ceil(d * hi) + 2):
            a, b = (k - E8) / d, (k + E8) / d
            if b > lo and a < hi: zones.append((a, b))
    zones.sort(); cur = lo
    for a, b in zones:
        if a > cur: return True
        cur = max(cur, b)
    return cur < hi

sets = [(1,2,3,4,5,6,7), (1,2,3,4,5,7,12), (1,4,5,6,7,11,13), (2,4,6,8,10,12,14), (2,4,6,8,10,14,24), (3,6,9,12,15,18,21)]
rnd = random.Random(113); c = Counter(); bad = []
eps, w = F(1, 10**6), F(1, 100)
for T in sets:
    # its simple pinches in (0, 1/2]
    pts = sorted({F(8 * k + 1, 8 * d) for d in T for k in range(d) if 0 < F(8*k+1, 8*d) <= F(1, 2)})
    for t0 in pts:
        lead, trail = edges(T, t0)
        if not (len(lead) == 1 and len(trail) == 1): continue
        if any(pos(d * t0) < E8 or pos(d * t0) > 1 - E8 for d in T): continue
        m = 1 - t0; ml, mt = edges(T, m)
        c['simple pinches'] += 1
        c['mirror is the same pair, roles swapped'] += (ml == trail and mt == lead)
        for _ in range(200):
            D = [rnd.randint(-5, 5) for _ in T]
            for sgn in (1, -1):
                R = [d + sgn * eps * x for d, x in zip(T, D)]
                a, b = lonely_near(R, t0, w), lonely_near(R, m, w)
                key = ('t0 opens' if a else '') + (' mirror opens' if b else '')
                c[(sgn, key or 'neither')] += 1
                if not (a or b): bad.append((T, t0, D, sgn))
for k, v in sorted(c.items(), key=str): print(k, v)
print("neither opens (should be only directions tangent to the wall):", len(bad))
for x in bad[:10]:
    T, t0, D, sgn = x; lead, trail = edges(T, t0)
    a, b = lead[0], trail[0]; ia, ib = T.index(a), T.index(b)
    print("  ", T, t0, D, sgn, "wall normal . D =", D[ib] * (8 * floor(a * t0) + 1) - D[ia] * (8 * ceil(b * t0) - 1))
nz = 0
for T, t0, D, sgn in bad:
    lead, trail = edges(T, t0); a, b = lead[0], trail[0]; ia, ib = T.index(a), T.index(b)
    nz += (D[ib] * (8 * floor(a * t0) + 1) - D[ia] * (8 * ceil(b * t0) - 1)) != 0
print("'neither' cases with the direction NOT tangent to the wall:", nz)
