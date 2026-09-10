#!/usr/bin/env python3
"""WHERE 248/1599 COMES FROM.  Exact Fraction, no float on any decision path.

E* = (2,6,7,8,10,13,14): five speeds on the grid 2*T1 = {2,4,6,8,10,12,14}, two off (7,13).
A GENERIC two-runner deviation would give (3/4)^2 |G(2*{1,3,4,5,7})| = 369/8960; the actual
is 93/14560.  Exact ratio 248/1599.  The off-grid speeds carry exactly two relations to the
grid:  2*7 = 14  (height 2)  and  6 + 7 = 13  (height 1).

Stage 1: break each relation by an infinitesimal perturbation and see what is recovered.
Stage 2: sweep every pair (x,y) added to the grid and locate the minimisers of |G|.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd
from functools import reduce

def gmeas(E):
    iv = []
    for e in E:
        for k in range(0, e + 1):
            lo, hi = max(F(8 * k - 1, 8 * e), F(0)), min(F(8 * k + 1, 8 * e), F(1))
            if lo < hi: iv.append((lo, hi))
    iv.sort(); mg = []
    for lo, hi in iv:
        if mg and lo <= mg[-1][1]: mg[-1][1] = max(mg[-1][1], hi)
        else: mg.append([lo, hi])
    cur = tot = F(0)
    for lo, hi in mg:
        if cur < lo: tot += lo - cur
        cur = max(cur, hi)
    return tot + (1 - cur if cur < 1 else 0)

def norm(E):
    g = reduce(gcd, E); return sorted(x // g for x in E)

GRID = [2, 6, 8, 10, 14]
EX   = [2, 6, 7, 8, 10, 13, 14]
GEN  = F(9, 16) * gmeas(norm(GRID))
ACT  = gmeas(EX)

print("STAGE 0 -- the baseline")
print(f"  |G(grid five)| = {gmeas(norm(GRID))}")
print(f"  generic 2-dev  = (3/4)^2 * that = {GEN} = {float(GEN):.6f}")
print(f"  actual |G(E*)| = {ACT} = {float(ACT):.6f}")
print(f"  ratio          = {ACT/GEN}   (this is the 248/1599)\n")

print("STAGE 1 -- break the relations, one at a time, by perturbing a speed off it")
def perturb(idx, q):
    E = [q * x for x in EX]; E[idx] -= 1
    return gmeas(norm(E))
labels = {2: "7   (breaks BOTH 2*7=14 and 6+7=13)", 5: "13  (breaks only 6+7=13)"}
for idx in (2, 5):
    vals = [perturb(idx, q) for q in (48, 96, 192)]
    stable = len(set(vals)) == 1
    v = vals[0]
    print(f"  perturb speed {labels[idx]:<40} |G| = {str(v):>14} = {float(v):.6f}"
          f"   {'(stable)' if stable else '(NOT stable: ' + str(vals) + ')'}")
    print(f"      recovery vs actual: x{float(v/ACT):.3f}      "
          f"vs generic: {float(v/GEN):.4f} of it")
# break both
E = [96 * x for x in EX]; E[2] -= 1; E[5] -= 5
both = gmeas(norm(E))
print(f"  perturb BOTH 7 and 13                            |G| = {str(both):>14} = "
      f"{float(both):.6f}")
print(f"      recovery vs actual: x{float(both/ACT):.3f}      vs generic: "
      f"{float(both/GEN):.4f} of it\n")

print("STAGE 2 -- every pair (x,y) added to the grid: who minimises |G|?")
rows = []
for x, y in combinations(range(1, 41), 2):
    if x in GRID or y in GRID: continue
    T = sorted(GRID + [x, y])
    if len(set(T)) != 7: continue
    if reduce(gcd, T) != 1: continue
    if not any(e % 8 == 0 for e in T): continue
    g = gmeas(T)
    rel = sum(1 for a, b, c in combinations(T, 3) if a + b == c)
    dbl = sum(1 for a in T for b in T if a != b and 2 * a == b)
    rows.append((g, x, y, rel, dbl))
rows.sort()
print(f"  {len(rows)} admissible pairs.  Ten smallest |G|:")
print("     x   y        |G| exact        |G|      3-term rels   doublings")
for g, x, y, rel, dbl in rows[:10]:
    mark = "  <- E*" if (x, y) == (7, 13) else ""
    print(f"    {x:>2}  {y:>2}   {str(g):>16}  {float(g):.6f}      {rel:>2}"
          f"            {dbl:>2}{mark}")
print(f"\n  largest |G|: {float(rows[-1][0]):.6f} at ({rows[-1][1]},{rows[-1][2]}), "
      f"rels={rows[-1][3]}, doublings={rows[-1][4]}")
import statistics
print(f"  correlation check -- mean |G| by 3-term relation count:")
from collections import defaultdict
d = defaultdict(list)
for g, x, y, rel, dbl in rows: d[rel].append(float(g))
for r in sorted(d):
    print(f"    rels={r}: n={len(d[r]):>3}  mean |G|={statistics.mean(d[r]):.6f}  "
          f"min={min(d[r]):.6f}")

# ---------------------------------------------------------------- STAGE 3
def stage3():
    """CLOSED FORMS for the two named resonance families, and what they actually contribute.

    f-hat(k) = -sin(pi k/4)/(pi k).  Two Bernoulli-polynomial identities, valid on [0,2pi]:
        sum_{m>=1} cos(m x)/m^2 = pi^2/6 - pi x/2 + x^2/4
        sum_{m>=1} sin(m x)/m^3 = (x^3 - 3 pi x^2 + 2 pi^2 x)/12
    give EXACT RATIONALS, no transcendentals surviving.

      support 2, pair (a,b) coprime:  sum_{m!=0} fhat(mb) fhat(ma) = 1/(4b) - 1/16   (a+b<=8)
      support 3, all +-1:             sum_{m>=1} fhat(m)^3 = -1/64
        [ sin^3 = (3 sin - sin 3)/4 ; sum sin(m pi/4)/m^3 = 7 pi^3/256 ,
          sum sin(3m pi/4)/m^3 = 5 pi^3/256 ; so sum sin^3(m pi/4)/m^3 = pi^3/64 ]
    """
    import math
    print("\nSTAGE 3 -- closed forms for the two named families")
    fh = lambda k: -math.sin(math.pi * k / 4) / (math.pi * k)
    num3 = sum(fh(m) ** 3 for m in range(1, 200001))
    num2 = 2 * sum(fh(2 * m) * fh(m) for m in range(1, 200001))
    print(f"  sum fhat(m)^3        : closed form {F(-1,64)} = {float(F(-1,64)):.9f}"
          f"   numeric {num3:.9f}   {'MATCH' if abs(num3 + 1/64) < 1e-6 else 'DIFFERS'}")
    print(f"  sum_{{m!=0}} fhat(2m)fhat(m): closed form {F(1,16)} = {float(F(1,16)):.9f}"
          f"   numeric {num2:.9f}   {'MATCH' if abs(num2 - 1/16) < 1e-6 else 'DIFFERS'}")
    C1 = F(1, 16) * F(3, 4) ** 5                 # 2*7=14, support 2, 5 free coords
    C2 = 2 * F(-1, 64) * F(3, 4) ** 4            # 6+7=13, support 3, 4 free coords, +-p
    print(f"\n  contribution of  2*7 = 14   : {C1} = {float(C1):+.6f}")
    print(f"  contribution of  6 + 7 = 13 : {C2} = {float(C2):+.6f}")
    print(f"  their sum                   : {C1 + C2} = {float(C1 + C2):+.6f}")
    deficit = ACT - GEN
    print(f"  the deficit to explain      : {deficit} = {float(deficit):+.6f}")
    print(f"\n  the two lowest-height families give the WRONG SIGN and "
          f"{float(abs((C1+C2)/deficit)):.1%} of the magnitude.")
    print("  So: the perturbation test attributes the factor to ALL resonances involving")
    print("  7 or 13, not to the two lowest-height ones.  Low height is not the carrier.")

stage3()
