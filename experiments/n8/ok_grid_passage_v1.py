#!/usr/bin/env python3
"""THE PASSAGE LAW.  Exact Fraction, no float.

Sweeping one speed off a tight instance, |G| does NOT open gradually -- it JUMPS to a
constant.  Conjecture from the AP data: breaking the resonance makes that runner generic
against the other six, so it deletes exactly 3/4 of their good set:

        |G(T with a_j perturbed)|  =  (3/4) * |G(T \\ {j})|.

Tested here for all three tight instances and all seven runners, exactly.
"""
from fractions import Fraction as F
from math import gcd
from functools import reduce

def gmeas(E):
    iv = []
    for e in E:
        for k in range(0, e + 1):
            lo, hi = max(F(8 * k - 1, 8 * e), F(0)), min(F(8 * k + 1, 8 * e), F(1))
            if lo < hi: iv.append((lo, hi))
    iv.sort(); merged = []
    for lo, hi in iv:
        if merged and lo <= merged[-1][1]: merged[-1][1] = max(merged[-1][1], hi)
        else: merged.append([lo, hi])
    cur = tot = F(0)
    for lo, hi in merged:
        if cur < lo: tot += lo - cur
        cur = max(cur, hi)
    return tot + (1 - cur if cur < 1 else 0)

def norm(E):
    g = reduce(gcd, E); return sorted(x // g for x in E)

TIGHT = {"T1": [1,2,3,4,5,6,7], "T2": [1,2,3,4,5,7,12], "T3": [1,4,5,6,7,11,13]}

print("PASSAGE LAW:  |G(T, a_j perturbed)|  ==  (3/4) |G(T minus j)| ?\n")
bad = 0
for name, T in TIGHT.items():
    print(f"{name} = {T}   |G| = {gmeas(T)}")
    for j in range(7):
        six = norm([T[i] for i in range(7) if i != j])
        rhs = F(3, 4) * gmeas(six)
        # perturb a_j by -1/q for a large q: q*T with the j-th entry reduced by 1
        row = []
        for q in (48, 96, 192):
            E = [q * T[i] for i in range(7)]; E[j] -= 1
            row.append(gmeas(norm(E)))
        ok = all(x == rhs for x in row)
        bad += (not ok)
        print(f"   drop {T[j]:>2}: |G(six)| = {str(gmeas(six)):>10}"
              f"   3/4 * that = {str(rhs):>10}"
              f"   perturbed = {str(row[0]):>10}  {'MATCH' if ok else 'differs ' + str(row)}")
    print()
print(f"mismatches: {bad} / 21")

# ------------------------------------------------------------------ does it MULTIPLY?
def part_two():
    print("\nDoes the passage law MULTIPLY?   two runners off the grid, both generic:")
    print("   conjecture  |G| = (3/4)^2 * |G(T minus {i,j})|\n")
    from itertools import combinations
    bad = tot = 0
    for name, T in TIGHT.items():
        for i, j in combinations(range(7), 2):
            five = norm([T[k] for k in range(7) if k not in (i, j)])
            rhs = F(9, 16) * gmeas(five)
            q = 96
            E = [q * T[k] for k in range(7)]
            E[i] -= 1; E[j] -= 5              # two INDEPENDENT generic perturbations
            got = gmeas(norm(E))
            tot += 1
            if got != rhs:
                bad += 1
                if bad <= 6:
                    print(f"   {name} drop ({T[i]},{T[j]}): predicted {rhs} "
                          f"({float(rhs):.6f})  got {got} ({float(got):.6f})")
    print(f"\n   mismatches: {bad} / {tot}")
    print("   -> the product law is NOT exact; the 3/4 factor is per-runner only when the"
          "\n      perturbed runner is generic AGAINST THE WHOLE REST, which two"
          "\n      simultaneous perturbations need not be.")

    print("\nThe extremum as a grid deviation:")
    EX = [2, 6, 7, 8, 10, 13, 14]
    on = [2, 6, 8, 10, 14]
    print(f"   E* = {EX}, on grid 2*T1: {on}, off: [7, 13]")
    print(f"   |G(E*)|            = {gmeas(EX)} = {float(gmeas(EX)):.6f}")
    print(f"   (3/4)^2 |G(on)|    = {F(9,16)*gmeas(norm(on))} "
          f"= {float(F(9,16)*gmeas(norm(on))):.6f}   <- what GENERIC deviation would give")
    print(f"   ratio actual/generic = {float(gmeas(EX) / (F(9,16)*gmeas(norm(on)))):.4f}")
    print("   the two off-grid speeds are NOT generic: 13 = 6+7 and 7 = 14/2 are resonant"
          "\n   with the on-grid part, which is exactly why E* is the extremum.")

part_two()
