"""Is simultaneous shadowing of all seven flanks over-determined by divisibility?

At flank e (integer differences), the ratio d/e in lowest terms is a/c with c = e/gcd(d,e).
Its blocked openings mod c are {k : circDist((a/c)(k+1/8)) < 1/8}; over a full period of e
openings it blocks a FIXED FRACTION of them, depending on c.

(1) the blocking density as a function of c -- small c (i.e. large gcd(d,e)) blocks MORE;
(2) the budget: shadowing e needs total blocking >= 1 + (m-1)/e, where m of the ratios block
    opening k = 0 (every ratio below 1 does), so overlap there is forced waste;
(3) the divisibility reading: high density needs gcd(d_j, e) large, i.e. the other differences
    must share large factors with e -- required SIMULTANEOUSLY at all seven flanks.
"""
from fractions import Fraction as F
from math import gcd
TH = F(1, 8)
def cd(x):
    f = x % 1; return min(f, 1 - f)
def density(c):
    """fraction of openings blocked by a ratio with denominator c (same for every numerator a
    coprime to c: the phases are an equally spaced c-grid, only the offset a/(8c) shifts)."""
    best = None
    for a in range(1, c + 1):
        if gcd(a, c) != 1: continue
        n = sum(1 for k in range(c) if cd(F(a, c) * (k + TH)) < TH)
        best = n if best is None else max(best, n)
    return F(best, c) if best is not None else F(0)
print("(1) blocking density by denominator c  (c = e/gcd(d,e))")
print("    c :  density   = blocked/c")
for c in range(1, 25):
    d = density(c)
    print(f"   {c:3} :  {str(d):8} = {float(d):.4f}")
print()
print("    -> small c blocks far more than the large-c limit of 1/4.")
print("       c = e/gcd(d,e) is small exactly when gcd(d,e) is LARGE.")
print()
print("(2) the budget at a flank: 6 ratios, all below 1 blocking k=0")
print("    need sum(density) >= 1 + (m-1)/e   with m = #ratios blocking k = 0")
for e in (8, 12, 16, 20, 30):
    print(f"    e={e:3}: six density-1/4 ratios give 1.50 vs requirement {1 + 5/e:.3f}"
          f"  -> {'enough' if 1.5 >= 1 + 5/e else 'SHORT'}")
print()
print("(3) what the eighth pattern actually spends (flank 8, ratios m/8):")
for m in (1, 3, 4, 5, 7):
    c = 8 // gcd(m, 8)
    print(f"    d={m}: gcd(d,8)={gcd(m,8)}, c={c}, density={density(c)} = {float(density(c)):.4f}")
tot = sum(density(8 // gcd(m, 8)) for m in (1, 3, 4, 5, 7))
print(f"    total density {tot} = {float(tot):.4f}   requirement 1 + 4/8 = 1.5   -> {'exactly tight' if tot == F(3,2) else 'slack ' + str(tot - F(3,2))}")
