"""At each runner's cascade isolation point, how close is the circle geometry to a grid pattern?  For every subject k of
random arrangements: positions p_j (fractions of a lap) of the other seven at the event; nearest eighth m_j/8 of each;
the largest deviation |p_j - m_j/8| (the pinner is exactly on an edge, deviation 0); whether the nearest eighths are
distinct (a grid pattern: the seven nonzero eighths, one runner each).  GridPairN applies (lonely at t or its partner)
when the geometry is within 1/56 of such a pattern.  Exact positions; the summaries are counts."""
import random
from fractions import Fraction as F
from collections import Counter
from circle_deform_v1 import iso

rnd = random.Random(8); rows = []
for _ in range(400):
    V = sorted(rnd.sample(range(1, 300), 8))
    for k in range(8):
        t, pos, setter, dm = iso(V, k)
        m = {j: round(8 * p) for j, p in pos.items()}
        dev = max(abs(p - F(m[j], 8)) for j, p in pos.items())
        distinct = len(set(x % 8 for x in m.values())) == 7 and all(x % 8 for x in m.values())
        rows.append((dev, distinct))
n = len(rows)
print(f"events {n} (400 arrangements x 8 subjects)")
print(f"  grid pattern (nearest eighths distinct and nonzero): {sum(d for _, d in rows)}")
for th in (F(1, 56), F(1, 32), F(1, 16)):
    print(f"  within {th} of its nearest eighths: {sum(1 for dv, _ in rows if dv <= th)};  and a grid pattern: {sum(1 for dv, d in rows if dv <= th and d)}")
print("  largest deviation, histogram in 1/64 units:", sorted(Counter(min(int(dv * 64), 8) for dv, _ in rows).items()))
