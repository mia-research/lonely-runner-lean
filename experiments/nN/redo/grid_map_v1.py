"""Owner: map how the grid achieves isolation, if there is a pattern; then (next) how the cascade maps those isolation
points when the speeds are moved off grid, as with the AP.  Here: random GRIDS (eight positive whole-number speeds whose
residues mod 8 are all different; the reduced speeds then form a complete residue system), every runner as subject,
the complete lonely set over one period [0, 1/g) exactly (BSM: blocked = union of open zones, clear set closed).
Per runner: the lonely components (as fractions of the period), which contain a phi(8) instant a/(8g), a in {1,3,5,7},
how long each is, and the cascade's isolation instant.  Exact (Fraction)."""
import random
from fractions import Fraction as F
from math import gcd, floor, ceil
from functools import reduce
from collections import Counter
from arrangement_lib import readings, cascade

def lonely_set(ds, P):
    """closed lonely components of readings ds in [0, P]"""
    Z = []
    for d in ds:
        for k in range(0, ceil(d * P) + 2):
            lo, hi = (k - F(1, 8)) / d, (k + F(1, 8)) / d
            if hi > 0 and lo < P: Z.append((lo, hi))
    Z.sort(); comps = []; cur = F(0)
    for lo, hi in Z:
        if hi <= cur: continue
        if lo >= cur and cur > 0: comps.append((cur, min(lo, P)))
        cur = max(cur, hi)
        if cur >= P: break
    return comps

def random_grid(rnd, top):
    while True:
        V = sorted(rnd.sample(range(1, top), 8))
        if len(set(v % 8 for v in V)) == 8: return V

if __name__ == '__main__':
    rnd = random.Random(31)
    stats = Counter(); only_phi = 0; tot = 0; comp_counts = Counter(); cascade_at_phi = 0; ex = []
    for _ in range(150):
        V = random_grid(rnd, 120)
        g = reduce(gcd, [b - a for a in V for b in V if b > a]); P = F(1, g)
        for k in range(8):
            ds = readings(V, k); tot += 1
            C = lonely_set(ds, P)
            phi = [F(a, 8 * g) for a in (1, 3, 5, 7)]
            with_phi = [c for c in C if any(c[0] <= x <= c[1] for x in phi)]
            others = [c for c in C if c not in with_phi]
            comp_counts[(len(with_phi), len(others))] += 1
            if not others: only_phi += 1
            t, mv = cascade(ds)
            cascade_at_phi += any(t == x for x in phi)
            if len(ex) < 4 and others:
                ex.append((V, k, [(float(a * g), float(b * g)) for a, b in C]))
    print(f"grids 150 x 8 runners = {tot} subjects")
    print(f"  lonely only in the components through the phi(8) instants a/(8g): {only_phi}")
    print(f"  (components through phi(8) instants, other components) per subject: {sorted(comp_counts.items())[:20]}")
    print(f"  the cascade's isolation is exactly a phi(8) instant: {cascade_at_phi}")
    for V, k, C in ex:
        print(f"  e.g. V {V}, runner {k}: components (as fractions of the period) {[(round(a,4), round(b,4)) for a, b in C][:10]}")
