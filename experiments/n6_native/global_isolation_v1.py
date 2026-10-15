#!/usr/bin/env python3
"""E44: global isolation at orders 3..7 (framework: ConstructionN/Instants.lean - isolation at p/n iff gcd(p,n) = 1,
phi(n) instants, none off the grid). For each n: the instants p/n; at each, the arrangement of the n runners (residue
r of a speed goes to position r p mod n: multiplication by the unit p); mirror pairs p <-> n - p (time reversal);
the cycle type of r -> r p on Z/n; for the subject at 0, the two neighbours at distance exactly 1/n (residues
+-p^{-1}); for the AP disparities 1..n-1 (subject 0): which runner enters (reads 1/n) and which leaves
(reads (n-1)/n) at p/n."""
from math import gcd
def cycles(p, n):
    seen = set(); out = []
    for r in range(n):
        if r in seen: continue
        c = 0; x = r
        while x not in seen: seen.add(x); x = x * p % n; c += 1
        out.append(c)
    return sorted(out, reverse=True)
for n in range(3, 8):
    units = [p for p in range(1, n) if gcd(p, n) == 1]
    print(f"== n = {n}: phi(n) = {len(units)}; instants p/n for p in {units}; mirror pairs {sorted({tuple(sorted((p, n - p))) for p in units})}")
    print(f"   all nonzero residues units (phi = n-1): {len(units) == n - 1}; unit group order {len(units)}, element orders {[next(k for k in range(1, n) if pow(p, k, n) == 1) for p in units]}")
    for p in units:
        inv = pow(p, -1, n)
        enter = [d for d in range(1, n) if d * p % n == 1]; leave = [d for d in range(1, n) if d * p % n == n - 1]
        print(f"   p = {p}: arrangement r -> {p} r, cycle type {cycles(p, n)}; subject's neighbours: residues {inv} and {n - inv}; AP: runner {enter[0]} enters, runner {leave[0]} leaves")
