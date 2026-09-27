"""E137: the 42 band sets to 24 left by AP classes + two-block + three-block, through the cascade: landing R*, flank,
laps, positions; the natural denominator of the readings in units of d_min (the finer grid); which block level K
(general lonely_eight_of_blocks at (8K+1)/(8e), any K <= 6) holds."""
import itertools
from fractions import Fraction as F
from math import floor, lcm
from collections import Counter
from proved_union_band_v1 import block
from ap_pairs_vs_late_v1 import class_status
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def cascade(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return 8 * T[0] * t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
rows = []
for T in itertools.combinations(range(1, 25), 7):
    if not (7 * T[0] < T[-1] <= 9 * T[0]): continue
    s = [F(d, T[0]) for d in T]
    if any(class_status(s, c) == 'works' for c in (1, 3, 5, 7)) or block(T, 1) or block(T, 2): continue
    R = cascade(T); laps = tuple(int(x * R // 8) for x in s); flank = [i for i in range(7) if (s[i] * R) % 8 == 1]
    K = next((K for K in range(3, 7) if block(T, K)), None)
    rows.append((T, R, flank, laps, K, T[0]))
print(len(rows), "sets; denominators d_min:", Counter(r[5] for r in rows))
print("landing R*:", Counter('%d-%d' % (floor(r[1]), floor(r[1]) + 1) for r in rows))
print("block level K (3..6) at some reading:", Counter(r[4] for r in rows))
print("landing laps:", Counter(r[3] for r in rows).most_common(10))
for T, R, fl, laps, K, _ in rows:
    print("  ", T, "R* = %s = %.4f" % (R, float(R)), "flank rank", fl, "laps", laps, "block K", K)
