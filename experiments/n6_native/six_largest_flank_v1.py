#!/usr/bin/env python3
"""Primitive SixResidual sets whose LARGEST element carries no certificate (residue search,
k < max S). Lists them with their certificates at other flanks. Exact integers."""
import sys, math, importlib.util
from itertools import combinations
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
HI = int(sys.argv[1]); tot = bad = 0
for S in combinations(range(1, HI + 1), 5):
    if math.gcd(*S) != 1 or not r.six_residual(S): continue
    tot += 1
    certs = r.certificates(S)
    if not any(b == max(S) for b, _ in certs):
        bad += 1
        if bad <= 40:
            g = {d: (math.gcd(d, 6), d % 6) for d in S}
            print(" ", S, "flanks with certs:", sorted({b for b, _ in certs}), "gcd/mod6:", g)
print(f"HI={HI}: residual={tot} largest-flank failures={bad}")
