#!/usr/bin/env python3
"""Cell reduction at a divisible largest flank e = 6E (unique multiple of 6, others d = 6q + s).
Claim tested: opening j = uE + i (0 <= i < E, 0 <= u < 6) clears d  iff
  (a_d(i) + s*u) mod 6 not in {0, 5},   a_d(i) = floor(((d*i + q) mod 6E) / E),
so the flank works iff some i has a(i) in G_s = {a in (Z/6)^4 : exists u, all (a_d + s_d u) mod 6 not in {0,5}}.
Checks the per-opening identity and the equivalence exhaustively on primitive SixResidual sets.
Exact integers."""
import sys, math, importlib.util
from itertools import combinations, product
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
HI = int(sys.argv[1])
def good_set(s):
    return {a for a in product(range(6), repeat=4)
            if any(all((a[t] + s[t] * u) % 6 not in (0, 5) for t in range(4)) for u in range(6))}
G = {}
n = mism_open = mism_flank = 0
for S in combinations(range(1, HI + 1), 5):
    if math.gcd(*S) != 1 or not r.six_residual(S): continue
    e = S[-1]
    if not (e % 6 == 0 and sum(d % 6 == 0 for d in S) == 1): continue
    n += 1; E = e // 6; rest = S[:-1]
    s = tuple(d % 6 for d in rest); q = tuple(d // 6 for d in rest)
    if s not in G: G[s] = good_set(s)
    direct_ok = False; cell_ok = False
    for i in range(E):
        a = tuple(((d * i + qq) % (6 * E)) // E for d, qq in zip(rest, q))
        if a in G[s]: cell_ok = True
        for u in range(6):
            j = u * E + i
            direct = all(e <= (d * (6 * j + 1)) % (6 * e) <= 5 * e for d in rest)
            cell = all((a[t] + s[t] * u) % 6 not in (0, 5) for t in range(4))
            if direct != cell: mism_open += 1
            direct_ok |= direct
    if direct_ok != cell_ok: mism_flank += 1
print(f"HI={HI}: divisible-largest residual sets={n}; per-opening mismatches={mism_open}; per-flank mismatches={mism_flank}")
for s, g in sorted(G.items()):
    print(f"  residues {s}: |G| = {len(g)} of 1296 cell vectors ({len(g)/1296:.3f})")
