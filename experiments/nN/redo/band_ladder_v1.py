"""E151: why the band's fast group is clear inside the slow group's first block, followed with the cascade.
(1) derived: every lap-1 exit 9/g of a fast reading g (above the largest gap) lies in [1, 7/s_top]: check.
(2) the least block level K (some reading e with every ratio d/e in U_k [(8k+1)/(8K+1), (8k+7)/(8K+1)]) against the
    cascade's landing lap; and whether the landing is in the slow group's first block.
(3) when level 1 fails: the top four dense (b1_remainder); level 2 met?
Populations: band to 24 (d_min = 1 units), late fine band shapes.  Exact."""
import itertools, random, sys
from fractions import Fraction as F
from math import floor
from collections import Counter
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade_R(s):
    t = F(1, 8)
    while True:
        way = [d for d in s if nd(d * t) < E8]
        if not way: return 8 * t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
def block_ok(s, e, K):
    return all(1 <= ((8 * K + 1) * d / e) % 8 <= 7 for d in s)
def study(pop, sets):
    C = Counter()
    for s in sets:
        gi = max(range(1, 7), key=lambda i: s[i] / s[i - 1]); S = s[:gi]; G = s[gi:]
        bad = sum(1 for g in G if g <= 9 and not (1 <= 9 / g <= 7 / S[-1]))
        C[(pop, '(1) lap-1 exits of G outside S\'s block: %d' % bad)] += 1
        R = cascade_R(s); f = next(i for i, d in enumerate(s) if (d * R) % 8 == 1); k = floor(s[f] * R / 8)
        Kmin = next((K for K in range(1, 12) if any(block_ok(s, e, K) for e in s)), None)
        inblk = F(S[-1], S[0]) <= 7 and 1 <= R <= 7 / S[-1]
        C[(pop, '(2) least block level %s, landing lap %d, %s' % (Kmin, k, 'in S\'s first block' if inblk else 'NOT in S\'s first block'))] += 1
        if Kmin != 1:
            dense = all(7 * s[i] < 9 * s[i - 1] for i in (4, 5, 6))
            C[(pop, '(3) level 1 fails: top four dense %s' % dense)] += 1
    return C
band = [tuple(F(d, T[0]) for d in T) for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1] <= 9 * T[0]]
D1 = 27720; rng = random.Random(41); late = set()
for sd in [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302)]:
    T = [int(round(x * D1)) for x in sd]
    for step in range(3000):
        U = list(T); i = rng.randrange(1, 7); U[i] += rng.randrange(-500, 501); U = sorted(set(U))
        if len(U) < 7 or U[0] != D1 or not (7 * D1 < U[-1] < 9 * D1): continue
        if clear_set([F(d, D1) for d in U], F(1), F(7)): continue
        T = U; late.add(tuple(U))
lateS = [tuple(F(d, D1) for d in U) for U in sorted(late)]
C = study('band24', band); C.update(study('late', lateS))
for k, v in sorted(C.items()): print("  %6d  %s" % (v, k))
