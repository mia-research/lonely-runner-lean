#!/usr/bin/env python3
"""Dimension reduction test at a divisible largest flank. For each pair of coordinates (t, t') and
residue pattern s, the FORCING pairs are (x, y) in (Z/6)^2 such that every completion a with
a_t = x, a_t' = y is good (a in G_s). Then, over primitive SixResidual sets (divisible largest),
counts how often the 2-D orbit i -> (a_t(i), a_t'(i)) hits a forcing pair, per coordinate pair."""
import sys, math, importlib.util
from itertools import combinations, product
from collections import Counter
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
def good(a, s): return any(all((a[t] + s[t] * u) % 6 not in (0, 5) for t in range(4)) for u in range(6))
cache = {}
def forcing(s, t, tp):
    key = (s, t, tp)
    if key not in cache:
        others = [k for k in range(4) if k not in (t, tp)]
        F = set()
        for x, y in product(range(6), repeat=2):
            ok = True
            for z, w in product(range(6), repeat=2):
                a = [0] * 4; a[t] = x; a[tp] = y; a[others[0]] = z; a[others[1]] = w
                if not good(tuple(a), s): ok = False; break
            if ok: F.add((x, y))
        cache[key] = F
    return cache[key]
HI = int(sys.argv[1]); n = 0; hit = Counter(); any_pair = 0; sizes = Counter()
for S in combinations(range(1, HI + 1), 5):
    if math.gcd(*S) != 1 or not r.six_residual(S): continue
    e = S[-1]
    if not (e % 6 == 0 and sum(d % 6 == 0 for d in S) == 1): continue
    n += 1; E = e // 6; rest = S[:-1]
    s = tuple(d % 6 for d in rest); q = tuple(d // 6 for d in rest)
    A = [tuple(((d * i + qq) % (6 * E)) // E for d, qq in zip(rest, q)) for i in range(E)]
    got = False
    for t, tp in combinations(range(4), 2):
        F = forcing(s, t, tp)
        sizes[(tuple(sorted((s[t], s[tp]))), len(F))] += 0
        if any((a[t], a[tp]) in F for a in A):
            hit[tuple(sorted((s[t], s[tp])))] += 1; got = True
    any_pair += got
print(f"HI={HI}: divisible-largest residual sets={n}; sets where SOME coordinate pair hits a forcing pair: {any_pair}")
print("  forcing-set sizes by residue pair:", sorted(set(k for k in sizes)))
print("  sets hit, by residue pair of the coordinates:", dict(hit))
