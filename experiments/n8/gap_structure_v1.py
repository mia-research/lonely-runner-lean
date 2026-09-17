"""The gap picture: what does the track look like at the instant each runner is isolated?

MANUSCRIPT_v9_1 section 4, line 205: "At any instant the eight runners cut the circle into eight cyclic
gaps summing to 1." Theorem 4.1: runner i is lonely IFF both gaps flanking it on the track are >= 1/8.

That gives an EXACT IDENTITY the reading picture does not visibly have:

    sum_j (g_j - 1/8) = 0   at every instant

-- the deficit of the gaps below 1/8 exactly equals the surplus of those above. This measures what that
identity does at isolation instants, and whether it constrains how many runners can be blocked at once.

A gap below 1/8 blocks the two runners adjacent to it, so with m deficient gaps at most 2m runners are
blocked and at least 8 - 2m are lonely. Measured here against the truth.
"""
import sys, random
from fractions import Fraction as F

n = 8; INV = F(1, n)
def fract(z): return z - (z.numerator // z.denominator)
def cd(z):    return min(fract(z), 1 - fract(z))

def gaps_at(speeds, t):
    """positions on the circle at t, sorted; the eight cyclic gaps."""
    pos = sorted(fract(F(v) * t) for v in speeds)
    g = [pos[(i + 1) % len(pos)] - pos[i] for i in range(len(pos) - 1)]
    g.append(1 - sum(g))
    return pos, g

def lonely_set(speeds, t):
    """runners (by speed) lonely at t, by the DEFINITION (differences), for cross-checking 4.1"""
    out = []
    for v in speeds:
        ds = [F(abs(v - w)) for w in speeds if w != v]
        if all(cd(d * t) >= INV for d in ds): out.append(v)
    return out

def lonely_by_gaps(speeds, t):
    """runners lonely by Theorem 4.1: both flanking gaps >= 1/8"""
    pos = sorted((fract(F(v) * t), v) for v in speeds)
    k = len(pos); out = []
    for i in range(k):
        left  = pos[i][0] - pos[i - 1][0] if i > 0 else pos[0][0] + 1 - pos[-1][0]
        right = pos[(i + 1) % k][0] - pos[i][0] if i < k - 1 else pos[0][0] + 1 - pos[-1][0]
        if left >= INV and right >= INV: out.append(pos[i][1])
    return sorted(out)

random.seed(20260917)
print("Theorem 4.1 cross-check, and the deficient-gap count\n")
agree = 0; tested = 0; rows = []
for _ in range(400):
    V = sorted(random.sample(range(0, 60), 8))
    t = F(random.randint(1, 400), random.randint(1, 60))
    if len(set(fract(F(v)*t) for v in V)) < 8: continue      # coincident positions: gaps degenerate
    tested += 1
    a = sorted(lonely_set(V, t)); b = lonely_by_gaps(V, t)
    if a == b: agree += 1
    else: rows.append((V, str(t), a, b))
print(f"  Theorem 4.1 (gaps) vs the definition (differences): agree {agree}/{tested}")
for r in rows[:3]: print("     DISAGREE", r)

print("\n  the identity: sum of (g - 1/8) over the eight gaps")
bad = 0
for _ in range(200):
    V = sorted(random.sample(range(0, 60), 8))
    t = F(random.randint(1, 400), random.randint(1, 60))
    _, g = gaps_at(V, t)
    if sum(g) != 1 or sum(x - INV for x in g) != 0: bad += 1
print(f"     instants where sum g = 1 and sum (g - 1/8) = 0 both hold: {200-bad}/200")

print("\n  deficient gaps m, and how many runners are lonely (bound: at least 8 - 2m)")
from collections import Counter
hist = Counter(); viol = 0; samples = 0
for _ in range(3000):
    V = sorted(random.sample(range(0, 60), 8))
    t = F(random.randint(1, 400), random.randint(1, 60))
    pos, g = gaps_at(V, t)
    if len(set(pos)) < 8: continue
    m = sum(1 for x in g if x < INV)
    L = len(lonely_by_gaps(V, t))
    samples += 1
    hist[(m, L)] += 1
    if L < 8 - 2*m: viol += 1
print(f"     samples {samples}; violations of 'lonely >= 8 - 2m': {viol}")
ms = Counter(m for (m, L), c in hist.items() for _ in range(c))
print(f"     distribution of m (deficient gaps): {dict(sorted(ms.items()))}")
z = sum(c for (m, L), c in hist.items() if L == 0)
print(f"     instants with NO runner lonely: {z}/{samples} = {100*z/samples:.1f}%")
mz = sorted({m for (m, L), c in hist.items() if L == 0})
print(f"     m values at which that happens: {mz}  (needs m >= 4 by the bound)")
