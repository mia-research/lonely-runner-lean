#!/usr/bin/env python3
"""Masks for a non-unit runner z = 7^w m (1 <= w <= a-2) in the abstraction of seven_abstract_v1.py:
rho = z k mod 49 in {7,...,42} (w = 1) or 0 (w >= 2); y in an open order-6 Farey cell, or y = 0 (w = a-2).
In band iff cell' in [7, 41] (z k mod 7^a = 6 7^(a-1) is impossible for unit k, m).  Output: minimal masks restricted
to runner 1's strategies, with their states."""
import pickle, sys
from fractions import Fraction as Fr
exec(open("seven_abstract_v1.py").read().split("units49 =")[0].replace("CMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 6", "CMAX = 6"))
d = pickle.load(open(sys.argv[1], "rb")); R = d["R"]
def restrict(m): return sum(1 << i for i, b in enumerate(R) if m >> b & 1)
zm = {}
for T in range(49):
    for rho in [0, 7, 14, 21, 28, 35, 42]:
        fls = list(enumerate(FL)) + ([(-1, (0,) * 6)] if rho == 0 else [])
        for fi, fl in fls:
            zm.setdefault(restrict(mask(T, fl, rho)), (T, fi, rho))
ms = sorted(zm, key=lambda m: bin(m).count("1"))
minimal = []
for m in ms:
    if not any((p & m) == p for p in minimal): minimal.append(m)
print("z distinct", len(zm), "minimal", len(minimal), "popcounts", sorted({bin(m).count('1') for m in minimal})[:8])
pickle.dump([(m, zm[m]) for m in minimal], open(sys.argv[2], "wb"))
