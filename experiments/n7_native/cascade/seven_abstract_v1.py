#!/usr/bin/env python3
"""Abstract state check for five units at every level a >= 4 (and mixed shapes), exact.

Instants k = c (1 + 7^(a-2) s), c in 1..6, s in Z/49 (the H_2 fold is additive for a >= 4).
A runner x (= u k_base) has: T = top two digits of x mod 7^a (cell of theta = x/7^a in 1/49ths), y = remainder in
[0,1), rho = x mod 49.  At instant (c, s): cell' = (c T + floor(c y) + s c rho) mod 49, in band iff cell' in [7, 41]
(theta' is never a multiple of 1/49 for a unit, a >= 3).  floor(c y) for c <= 6 depends only on the order-6 Farey
cell of y (y is never a Farey point).  Runner 1 = 1: T = 0, y in the first cell, rho = 1.
Writes the distinct masks; reports how many, and the minimal ones (by inclusion)."""
from fractions import Fraction as Fr
import itertools, pickle, sys
fpts = sorted({Fr(p, q) for q in range(1, 7) for p in range(0, q + 1)})
cells = [(fpts[i], fpts[i + 1]) for i in range(len(fpts) - 1)]
def floors(cell):
    m = (cell[0] + cell[1]) / 2
    return tuple(int(c * m) for c in range(1, 7))
FL = [floors(cl) for cl in cells]
CMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 6
strategies = [(c, s) for c in range(1, CMAX + 1) for s in range(49)]
def mask(T, fl, rho, closed42=False):
    m = 0
    for b, (c, s) in enumerate(strategies):
        cell = (c * T + fl[c - 1] + s * c * rho) % 49
        if 7 <= cell <= 41 or (closed42 and cell == 42): m |= 1 << b
    return m
units49 = [r for r in range(1, 49) if r % 7]
unit_masks = {}
for T in range(49):
    for fi, fl in enumerate(FL):
        for rho in units49:
            unit_masks.setdefault(mask(T, fl, rho), (T, fi, rho))
m1 = mask(0, FL[0], 1)
print("Farey cells", len(cells), "strategies", len(strategies), "distinct unit masks", len(unit_masks))
print("runner-1 mask popcount", bin(m1).count("1"))
# restrict to the strategies runner 1 allows, then keep inclusion-minimal masks
R = [b for b in range(len(strategies)) if m1 >> b & 1]
def restrict(m): return sum(1 << i for i, b in enumerate(R) if m >> b & 1)
um = {}
for m, st in unit_masks.items(): um.setdefault(restrict(m), st)
ms = sorted(um, key=lambda m: bin(m).count("1"))
minimal = []
for m in ms:
    if not any((p & m) == p for p in minimal): minimal.append(m)
print("restricted distinct", len(um), "inclusion-minimal", len(minimal), "bits", len(R))
pickle.dump({"R": R, "minimal": [(m, um[m]) for m in minimal], "nbits": len(R)}, open(sys.argv[1], "wb"))
