#!/usr/bin/env python3
"""As six_forcing_pairs_v1.py, for triples of coordinates: forcing triples are cell values on three
coordinates that make every completion good. Counts how many divisible-largest residual sets are
caught by some triple, and whether pairs+triples together catch all."""
import sys, math, importlib.util
from itertools import combinations, product
from collections import Counter
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
def good(a, s): return any(all((a[t] + s[t] * u) % 6 not in (0, 5) for t in range(4)) for u in range(6))
cache = {}
def forcing3(s, T):
    key = (s, T)
    if key not in cache:
        other = [k for k in range(4) if k not in T][0]
        F = set()
        for v in product(range(6), repeat=3):
            if all(good(tuple(v[T.index(k)] if k in T else z for k in range(4)), s) for z in range(6)):
                F.add(v)
        cache[key] = F
    return cache[key]
HI = int(sys.argv[1]); n = 0; caught = 0; byT = Counter(); sizes = {}
for S in combinations(range(1, HI + 1), 5):
    if math.gcd(*S) != 1 or not r.six_residual(S): continue
    e = S[-1]
    if not (e % 6 == 0 and sum(d % 6 == 0 for d in S) == 1): continue
    n += 1; E = e // 6; rest = S[:-1]
    s = tuple(d % 6 for d in rest); q = tuple(d // 6 for d in rest)
    A = [tuple(((d * i + qq) % (6 * E)) // E for d, qq in zip(rest, q)) for i in range(E)]
    got = False
    for T in combinations(range(4), 3):
        F = forcing3(s, T)
        lab = tuple(sorted(s[t] for t in T)); sizes[lab] = len(F)
        if any(tuple(a[t] for t in T) in F for a in A): byT[lab] += 1; got = True
    caught += got
print(f"HI={HI}: divisible-largest residual sets={n}; caught by some forcing triple: {caught}")
print("  forcing-triple counts (of 216) by residues:", sizes)
print("  sets caught, by residues of the triple:", dict(byT))
