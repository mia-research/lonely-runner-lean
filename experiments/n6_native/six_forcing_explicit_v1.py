#!/usr/bin/env python3
"""Explicit forcing regions at a divisible flank. For residues of the unit pair (1, 5) and the triple
(1, 3, 5), with the fourth coordinate's residue 2 or 4: list the forcing cell values and test simple
descriptions (sums/differences of cells mod 6). A cell vector is good iff some coarse shift u puts
every (a_t + s_t u) mod 6 in {1,2,3,4}."""
from itertools import product
from collections import Counter
def good(a, s): return any(all((a[t] + s[t] * u) % 6 not in (0, 5) for t in range(len(s))) for u in range(6))
def forcing(sub_s, rest_s):
    F = []
    for v in product(range(6), repeat=len(sub_s)):
        if all(good(v + w, sub_s + rest_s) for w in product(range(6), repeat=len(rest_s))): F.append(v)
    return F
for rest in [(3, 2), (3, 4)]:
    F = forcing((1, 5), rest)
    print(f"unit pair (1,5), others {rest}: forcing pairs {F}")
    print("   a1+a5 mod 6:", Counter((x + y) % 6 for x, y in F), " a1-a5 mod 6:", Counter((x - y) % 6 for x, y in F))
for rest in [(2,), (4,)]:
    F = forcing((1, 3, 5), rest)
    print(f"triple (1,3,5), other {rest}: {len(F)} forcing triples")
    byA3 = {}
    for x, z, y in F: byA3.setdefault(z, []).append((x, y))
    for z in sorted(byA3):
        pairs = byA3[z]
        print(f"   a3={z}: {len(pairs)} pairs (a1,a5); a1+a5 mod 6 values {sorted(Counter((x+y)%6 for x,y in pairs).items())}")
