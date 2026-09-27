"""E121: the band as two copies of the slowest runner's first block.  At R + 8 every reading s moves by 8 s, i.e. its
phase rotates by 8*{s}.  For each band set: is the first block [1,7] clear somewhere (copy 0)?  If not, which rotated
copy m (R + 8m, R in [1,7]) is the first with a clear instant?  Exhaustive to 40 and the late fine shapes.  Exact."""
import itertools
from fractions import Fraction as F
from collections import Counter
def clear_in(s, lo, hi):
    pts = {lo, hi}
    for x in s:
        k0 = int(lo * x // 8) - 1
        while True:
            for e in (8 * k0 + 1, 8 * k0 + 7):
                r = F(e) / x
                if lo <= r <= hi: pts.add(r)
            if F(8 * k0 - 1) / x > hi: break
            k0 += 1
    pts = sorted(pts)
    ok = lambda R: all(1 <= (x * R) % 8 <= 7 for x in s)
    return any(ok(p) for p in pts) or any(ok((a + b) / 2) for a, b in zip(pts, pts[1:]))
c = Counter()
for T in itertools.combinations(range(1, 41), 7):
    if not (7 * T[0] < T[-1] < 9 * T[0]): continue
    s = [F(d, T[0]) for d in T]
    m = next(m for m in range(0, 8) if clear_in(s, F(1 + 8 * m), F(7 + 8 * m)))
    c[m] += 1
print("band sets to 40: first copy with a clear instant:", sorted(c.items()))
D1 = 27720
for shape in [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.3091, 3.1726, 4.1869, 5.2226, 5.7861, 7.4385)]:
    s = [F(int(round(x * D1)), D1) for x in shape]
    print("  ", shape, [(m, clear_in(s, F(1 + 8 * m), F(7 + 8 * m))) for m in range(3)])
