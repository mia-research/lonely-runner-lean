"""Owner: global isolation holds at every GRID (reduced speeds a complete residue system mod 8, e.g. 1..7, 16), not only
at the progression; any arrangement deforms the circle geometry and relocates it.  Test the grid pair law exactly (BSM):
for a grid G (integers, residues mod 8 distinct, g = gcd of differences), subject k, and a perturbation V = G + delta,
the instants a/(8g), a in {1,3,5,7}, come in pairs (1,7), (3,5); predicted: for every subject and every small enough
perturbation, at least one instant of each pair survives as a lonely interval nearby.
Exact: near t_a = a/(8g), runner j's clear condition is an interval in t (its position stays in one lap); intersect all
seven, over t in [t_a - 1/(16 g M), t_a + 1/(16 g M)] with M the largest |reading|.  Report, per perturbation size, how
often each pair keeps a lonely instant, over random grids, subjects and directions."""
import random
from fractions import Fraction as F
from math import gcd, floor
from functools import reduce

def lonely_interval_near(V, k, ta, halfw):
    lo, hi = ta - halfw, ta + halfw
    for j in range(8):
        if j == k: continue
        w = V[j] - V[k]
        # need circDist(w t) >= 1/8 for t in [lo, hi]; w t moves monotonically; find the clear sub-interval containing
        # the lap of w*ta: positions in [m + 1/8, m + 7/8] with m = floor(w*ta)
        c = w * ta; m = floor(c)
        a, b = (m + F(1, 8)) / w, (m + F(7, 8)) / w
        if a > b: a, b = b, a
        lo, hi = max(lo, a), min(hi, b)
        if lo > hi: return None
    return (lo, hi)

def random_grid(rnd):
    while True:
        res = list(range(8)); rnd.shuffle(res)
        G = sorted(8 * rnd.randint(0, 12) + r for r in res)
        if len(set(G)) == 8 and len(set(x % 8 for x in G)) == 8: return [x + 8 for x in G]

if __name__ == '__main__':
    rnd = random.Random(7)
    for eps in (F(1, 1000), F(1, 100), F(1, 20), F(1, 8), F(1, 4)):
        tot = both = 0; p17 = p35 = 0; fail = []
        for _ in range(300):
            G = random_grid(rnd); g = reduce(gcd, [abs(a - b) for a in G for b in G if a != b])
            V = [x + eps * F(rnd.randint(-1000, 1000), 1000) for x in G]
            if sorted(V) != V or len(set(V)) < 8: continue
            M = max(V) - min(V)
            for k in range(8):
                tot += 1
                s17 = any(lonely_interval_near(V, k, F(a, 8 * g), F(1, 16 * g * M)) for a in (1, 7))
                s35 = any(lonely_interval_near(V, k, F(a, 8 * g), F(1, 16 * g * M)) for a in (3, 5))
                p17 += s17; p35 += s35; both += s17 and s35
                if not (s17 and s35) and len(fail) < 3: fail.append((G, [float(x) for x in V], k, s17, s35))
        print(f"perturbation up to {float(eps)} per speed: subjects {tot}; pair (1,7) survives {p17}; pair (3,5) survives {p35}; both {both}")
        for f in fail: print("   not both:", f)
