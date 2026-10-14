"""Mapping the 27.4% residue at n=5.

Residue = some NON-FLANK disparity divisible by 5 (plus wide ratio, d_max > 15).

The key algebra: for d = 5m the factor cancels,
      5m * a / (5e) = m * a / e,
so the 5-multiple is clear iff  m*a mod e  in [e/5, 4e/5]  -- MODULUS e, not 5e.
Non-multiples keep the old rule: d*a mod 5e in [e, 4e].
So the residue is a MIXED system: some conditions mod 5e, some mod e.
"""
import math
from itertools import combinations
from collections import Counter
from fractions import Fraction as F

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

def in_residue(c):
    e = c[-1]
    return any(d % 5 == 0 for d in c[:-1]) and e > 4*c[0] and e > 15

def n_open(c):
    e = c[-1]; M = 5*e
    return sum(1 for j in range(e) if all(e <= (d*(5*j+1)) % M <= 4*e for d in c))

hi = 50
sets = [c for c in combinations(range(1, hi+1), 4) if prim(c) and in_residue(c)]
print(f"residue sets in [1,{hi}]: {len(sets)}\n")

print("=== how many non-flank 5-multiples? ===")
print("  ", dict(sorted(Counter(sum(1 for d in c[:-1] if d % 5 == 0) for c in sets).items())))
print()
print("=== is the flank ALSO a multiple of 5? ===")
print("  ", dict(Counter(c[-1] % 5 == 0 for c in sets)))
print()
print("=== working openings: minimum over the residue ===")
mn = min(n_open(c) for c in sets)
tight = [c for c in sets if n_open(c) <= 2]
print(f"   min = {mn}   sets with <= 2 openings: {len(tight)}"
      + (f"   max elt among them {max(max(c) for c in tight)}" if tight else ""))
print()
print("=== the mixed system, made explicit on a sample ===")
print(f"{'set':>22} {'e':>4} {'5-mults (as m)':>16} {'#open':>6}")
for c in sets[:14]:
    e = c[-1]
    ms = [(d, d//5) for d in c[:-1] if d % 5 == 0]
    print(f"{str(c):>22} {e:>4} {str(ms):>16} {n_open(c):>6}")
print()
print("=== does gcd(m, e) matter?  (m = the 5-multiple over 5) ===")
byg = {}
for c in sets:
    e = c[-1]
    for d in c[:-1]:
        if d % 5: continue
        g = math.gcd(d // 5, e)
        t, s = byg.get(g, (0, 0))
        byg[g] = (t + 1, s + n_open(c))
print(f"{'gcd(m,e)':>9} {'instances':>10} {'mean #open':>11}")
for g in sorted(byg):
    t, s = byg[g]
    print(f"{g:>9} {t:>10} {s/t:>11.2f}")
