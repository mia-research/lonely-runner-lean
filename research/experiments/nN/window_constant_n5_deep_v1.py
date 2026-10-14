# P4 is the LARGE-RATIO tool: a clear window of length > 1/e contains a flank opening of e.
# For blockers (a,b,c) the criterion fires iff  d4 > 1/W(a,b,c).  Since d4 >= c, the criterion
# fires for EVERY d4 >= c as soon as  W(a,b,c) * c > 1.  So compute  min over triples of W*c.
# Exact rational arithmetic; W = longest interval of t in [0,1] clear of all three at 1/5.
from fractions import Fraction as F
from itertools import combinations
import math
n = 5
def norm(x):
    fl = x - (x.numerator // x.denominator)
    return min(fl, 1 - fl)
def W(ds):
    pts = {F(0), F(1)}
    for d in ds:
        for k in range(0, d + 2):
            for off in (F(-1, n), F(1, n)):
                t = (F(k) + off) / F(d)
                if 0 <= t <= 1: pts.add(t)
    P = sorted(pts); best = F(0)
    for i in range(len(P) - 1):
        lo, hi = P[i], P[i + 1]
        if all(norm(F(d) * ((lo + hi) / 2)) >= F(1, n) for d in ds) and hi - lo > best:
            best = hi - lo
    return best
HI = 45
best = None; worst = []
for a, b, c in combinations(range(1, HI + 1), 3):
    if math.gcd(math.gcd(a, b), c) != 1: continue
    v = W((a, b, c)) * c
    if best is None or v < best:
        best = v; worst = [(a, b, c, v)]
    elif v == best:
        worst.append((a, b, c, v))
print(f"distinct blocker triples (gcd 1, entries <= {HI}):")
print(f"  min over triples of  W(a,b,c) * c  =  {best}  =  {float(best):.6f}")
print(f"  attained at {len(worst)} triples, e.g. {worst[:6]}")
print()
print("  >1  means P4 fires for EVERY larger flank -> the integer case would be closed by P4 alone")
print(f"  verdict: {'CLOSED' if best > 1 else 'NOT closed by P4 alone'}")
