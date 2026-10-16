#!/usr/bin/env python3
"""Check of TaxoEmpty_v1 against data: whenever the closer is the opener's own reading (classes K1s1, K1s2, K2s2),
the opener is the fastest runner (closer_same_forces_fastest); and K2a, K2s1 never occur (E78). Orders 4..7, the
exhaustive ranges of taxo_orders_v1."""
import math
from itertools import combinations
from collections import Counter
exec(open("taxo_orders_v1.py").read().split("H = {")[0])
H = {4: 90, 5: 50, 6: 30, 7: 22}
for n in (4, 5, 6, 7):
    same = Counter(); empty = 0
    for S in combinations(range(1, H[n] + 1), n - 1):
        if math.gcd(*S) != 1: continue
        k, (s, c), nm, Rs = taxo(S, n)
        if k in ("K1s1", "K1s2", "K2s2"): same[s == n - 1] += 1
        empty += k in ("K2a", "K2s1")
    print(f"n={n}: closer = opener -> opener fastest: {dict(same)}; K2a/K2s1 occurrences: {empty}")
