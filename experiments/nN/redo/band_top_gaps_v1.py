"""E122: the gaps the top reading's deviation opens.  s7 = 7 + eps (eps in (0,2)).  Just before the slowest runner's
window at 8m-1, the top's window ends at 7(8m-1)/s7, so G_m = [7(8m-1)/s7, 8m-1] is left to the other five readings.
Question to the oracle: is G_1 or G_2 ever fully covered by the other readings' windows -- both at once?
Exhaustive band sets to N, and fine random/extremal shapes.  Exact."""
import itertools, random
from fractions import Fraction as F
from collections import Counter
def uncovered(s, lo, hi):
    """points of [lo, hi] outside every window ((8k-1)/x, (8k+1)/x) of the readings s (open windows)."""
    pts = {lo, hi}
    for x in s:
        for k in range(int(lo * x / 8) - 1, int(hi * x / 8) + 2):
            for e in (8 * k - 1, 8 * k + 1):
                r = F(e) / x
                if lo <= r <= hi: pts.add(r)
    pts = sorted(pts)
    free = lambda R: all(not (8 * k - 1 < x * R < 8 * k + 1) for x in s for k in [round(x * R / 8)])
    for p in pts:
        if free(p): return p
    for a, b in zip(pts, pts[1:]):
        if free((a + b) / 2): return (a + b) / 2
    return None
def test(s):
    top = s[-1]; mid = s[1:-1]
    g1 = uncovered(mid, F(49) / top, F(7)); g2 = uncovered(mid, F(105) / top, F(15))
    return g1 is not None, g2 is not None
c = Counter(); ex = []
for T in itertools.combinations(range(1, 41), 7):
    if not (7 * T[0] < T[-1] < 9 * T[0]): continue
    s = [F(d, T[0]) for d in T]; r = test(s); c[r] += 1
    if r == (False, False) and len(ex) < 8: ex.append(T)
print("band sets to 40: (G1 has a free point, G2 has a free point):", sorted(c.items()))
print("   both covered, e.g.", ex)
rnd = random.Random(5); c2 = Counter(); ex2 = []
for trial in range(20000):
    d1 = rnd.randrange(40, 3000); top = rnd.randrange(7 * d1 + 1, 9 * d1)
    T = tuple(sorted([d1, top] + rnd.sample(range(d1 + 1, top), 5)))
    s = [F(d, T[0]) for d in T]; r = test(s); c2[r] += 1
    if r == (False, False) and len(ex2) < 5: ex2.append([round(float(x), 4) for x in s])
print("random fine shapes 20,000:", sorted(c2.items()), " both covered e.g.", ex2)
