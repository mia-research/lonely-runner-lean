"""Candidate RULE for the residue: put a in the middle of the multiples' band.

Conditions, with a = 5j+1:
  non-multiple d : d*a mod 5e  in [e, 4e]
  multiple  5m   : m*a mod e   in [e/5, 4e/5]        (the 5 cancels)

The multiples constrain a mod e; the non-multiples constrain a mod 5e.  Dichotomy: as j runs
over [0,e), a mod e hits EVERY residue once when 5 does not divide e, but only the e/5 residues
= 1 mod 5 (each five times) when 5 | e.

Rule tested: among the a that satisfy every multiple's band, take the one whose a mod e is
closest to e/2 (deepest inside the band).  Does it also clear the non-multiples?
"""
import math
from itertools import combinations
from fractions import Fraction as F

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

def in_residue(c):
    e = c[-1]
    return any(d % 5 == 0 for d in c) and e > 4*c[0] and e > 15

def clear_all(c, a, e):
    M = 5*e
    return all(e <= (d*a) % M <= 4*e for d in c)

def mult_ok(c, a, e):
    for d in c:
        if d % 5: continue
        m = d // 5
        r = (m*a) % e
        if not (F(e,5) <= r <= F(4*e,5)): return False
    return True

hi = 40
sets = [c for c in combinations(range(1, hi+1), 4) if prim(c) and in_residue(c)]
tot = rule_ok = mult_band_nonempty = 0
fails = []
for c in sets:
    e = c[-1]; tot += 1
    cands = [5*j+1 for j in range(e) if mult_ok(c, 5*j+1, e)]
    if cands: mult_band_nonempty += 1
    else: continue
    best = min(cands, key=lambda a: abs(F(a % e) - F(e,2)))
    if clear_all(c, best, e): rule_ok += 1
    elif len(fails) < 6: fails.append((c, best, best % e, e))
print(f"residue sets in [1,{hi}]: {tot}")
print(f"   sets where SOME a satisfies every multiple's band : {mult_band_nonempty}")
print(f"   of those, the 'deepest in band' a clears everything: {rule_ok}  ({100*rule_ok/mult_band_nonempty:.2f}%)")
print(f"   rule failures: {len(fails)} shown")
for c, a, r, e in fails: print(f"      {c}  e={e}  chosen a={a} (a mod e = {r})")
print()
print("=== how constrained is a?  counts of a passing each layer ===")
print(f"{'set':>20} {'e':>4} {'a: mult band':>13} {'a: all clear':>13}")
for c in sets[:12]:
    e = c[-1]
    mb = sum(1 for j in range(e) if mult_ok(c, 5*j+1, e))
    ac = sum(1 for j in range(e) if clear_all(c, 5*j+1, e))
    print(f"{str(c):>20} {e:>4} {mb:>13} {ac:>13}")
