"""Reach of the flank sum criterion (Prop 6.11) at order 8.

Criterion:  sum_{j in J} (2/n + 1/c_j) < 1,  with 1/c_j = 0 for an irrational ratio.
J = the non-integer ratios at a live flank, c_j the denominator of the fractional part.

Question asked: for which |J| and which denominator profiles can the criterion fire at all.
This is a property of the criterion, not of any arrangement -- it bounds the criterion's reach
from above regardless of what the census contains.
"""
from fractions import Fraction

n = 8
ell = Fraction(2, n)

# 1/c_j is smallest (best case for the criterion) when c_j is large or the ratio is irrational.
# The infimum of a term is therefore ell itself.  So |J| * ell < 1 is NECESSARY.
max_J = 0
while (max_J + 1) * ell < 1:
    max_J += 1
print(f"order n = {n}, arc length 2/n = {ell}")
print(f"largest |J| for which the criterion can fire at all : {max_J}")
print(f"  (|J| = {max_J+1} already gives sum >= {(max_J+1)*ell} >= 1 from the 2/n terms alone,")
print(f"   whatever the denominators)")
print()

# For each feasible |J|, the denominator budget left over.
for J in range(1, max_J + 1):
    budget = 1 - J * ell                     # sum of 1/c_j must be < budget
    # the easiest profile: all c_j equal
    cmin = None
    c = 1
    while c <= 10000:
        if J * Fraction(1, c) < budget:
            cmin = c
            break
        c += 1
    print(f"|J| = {J}: sum of 1/c_j must be < {budget}; "
          f"all-equal denominators need c_j >= {cmin}"
          + ("  (or irrational, 1/c = 0)" if cmin else ""))

print()
print("Consequence: at order 8 the criterion decides only flanks with at most three")
print("non-integer ratios.  Flanks with four or more are outside it by the 2/n terms alone,")
print("before any denominator is looked at.  This is a ceiling of the method, not a gap in")
print("its proof: no strengthening of the residue count moves it.")


# ---------------------------------------------------------------------------
# Practical reach: over every 8-subset of [1,20], the distribution of |J| per
# live flank, and how many live flanks the criterion actually decides.
from itertools import combinations
from math import gcd

def den(num, dn):                     # denominator of the fractional part of num/dn
    g = gcd(num % dn, dn)
    return dn // g

tot = 0
byJ = {}
fires = 0
for S in combinations(range(1, 21), 8):
    for e in S:
        others = [d for d in S if d != e]
        # live flank: no ratio == 0 mod n, i.e. no other d with d/e an integer multiple of 8
        if any(d % e == 0 and (d // e) % n == 0 for d in others):
            continue
        J = [d for d in others if d % e != 0]
        tot += 1
        byJ[len(J)] = byJ.get(len(J), 0) + 1
        s = sum(Fraction(2, n) + Fraction(1, den(d, e)) for d in J)
        if s < 1:
            fires += 1

print()
print("Practical reach, every 8-subset of [1,20], per LIVE FLANK:")
print(f"  live flanks              : {tot}")
print(f"  |J| distribution         : {dict(sorted(byJ.items()))}")
print(f"  decided by the criterion : {fires}  ({100*fires/tot:.3f}%)")

# Which |J| do the firings actually come from?  If they are all |J| <= 1, the
# criterion adds nothing in this range beyond Theorem 6.9 (one fractional ratio),
# which is already proved without any count.
fires_byJ = {}
for S in combinations(range(1, 21), 8):
    for e in S:
        others = [d for d in S if d != e]
        if any(d % e == 0 and (d // e) % n == 0 for d in others):
            continue
        J = [d for d in others if d % e != 0]
        s = sum(Fraction(2, n) + Fraction(1, den(d, e)) for d in J)
        if s < 1:
            fires_byJ[len(J)] = fires_byJ.get(len(J), 0) + 1
print(f"  firings by |J|           : {dict(sorted(fires_byJ.items()))}")
hi = [k for k in fires_byJ if k >= 2]
print(f"  firings with |J| >= 2    : {sum(fires_byJ[k] for k in hi)}"
      f"{'  -- none, so in this range the criterion decides nothing that' if not hi else ''}")
if not hi:
    print("                             Theorem 6.9 does not already decide.")

print()
print("SCOPE OF THE ABOVE.  Integer difference sets have no irrational ratios, so every")
print("1/c_j above is strictly positive.  The criterion's own stated contribution at order 8")
print("-- 'one, two or three irrational ratios never shadow a live flank' -- rests on the")
print("1/c_j = 0 terms and is NOT exercised by this range.  The finding is therefore:")
print("  * over integer differences in [1,20], the criterion decides nothing that Theorem 6.9")
print("    does not already decide without any count;")
print("  * its non-redundant content is confined to ratios off every lattice, and to large")
print("    denominators, neither of which occurs here.")
print("The |J| <= 3 ceiling holds in both regimes.")
