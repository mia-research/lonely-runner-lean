"""Prop 6.10, rational pair: check the two-step reduction.

Step 1 (no count, formalised via class_killer_int): if two lattice runners shadow a live
flank between them, each lies on the other's lattice, so their reduced denominators divide
each other -- hence c1 = c2.

Step 2 (a count, over ONE denominator): two runners of common denominator c cover all c
residues only when c = 2.

Both are checked here by direct enumeration of the shadowing relation.
"""
from fractions import Fraction
from math import gcd
from itertools import product

n = 8

def circDist(x: Fraction) -> Fraction:
    f = x - (x.numerator // x.denominator)
    return min(f, 1 - f)

def inway(f: Fraction, k: int, rho: Fraction) -> bool:
    # runner in the way at opening k of the flank: circDist(k*f + rho/n) < 1/n
    return circDist(k * f + rho / n) < Fraction(1, n)

CMAX = 14
pairs_shadow = []
for c1 in range(2, CMAX + 1):
    for c2 in range(2, CMAX + 1):
        for a1 in range(1, c1):
            if gcd(a1, c1) != 1: continue
            for a2 in range(1, c2):
                if gcd(a2, c2) != 1: continue
                f1, f2 = Fraction(a1, c1), Fraction(a2, c2)
                # the whole parts shift rho; sweep them mod n (verdict depends on rho mod n)
                for w1, w2 in product(range(n), repeat=2):
                    r1, r2 = w1 + f1, w2 + f2
                    L = (c1 * c2) // gcd(c1, c2)
                    if all(inway(f1, k, r1) or inway(f2, k, r2) for k in range(L)):
                        pairs_shadow.append((c1, c2, a1, a2, w1, w2))

print(f"denominators swept        : 2..{CMAX}, all reduced numerators, all whole parts mod {n}")
print(f"shadowing pairs found     : {len(pairs_shadow)}")
dens = sorted({(p[0], p[1]) for p in pairs_shadow})
print(f"denominator pairs (c1,c2) : {dens}")
unequal = [d for d in dens if d[0] != d[1]]
print(f"with c1 != c2             : {unequal}  -> step 1 {'HOLDS' if not unequal else 'FAILS'}")
nontwo = [d for d in dens if d != (2, 2)]
print(f"with (c1,c2) != (2,2)     : {nontwo}  -> step 2 {'HOLDS' if not nontwo else 'FAILS'}")
if pairs_shadow:
    fr = sorted({(Fraction(p[2], p[0]), Fraction(p[3], p[1])) for p in pairs_shadow})
    print(f"fractional parts realised : {[(str(a), str(b)) for a, b in fr]}")
    wp = sorted({(p[4], p[5]) for p in pairs_shadow})
    print(f"whole parts mod {n}         : {wp}   ({len(wp)} combinations)")

if pairs_shadow:
    unordered = {frozenset(x) if len(set(x)) > 1 else (x[0], x[1])
                 for x in [(p[4], p[5]) for p in pairs_shadow]}
    print(f"unordered whole-part pairs: {len(unordered)}  "
          f"-- the manuscript's 'exactly 4 such pairs, by whole part mod 8'")
