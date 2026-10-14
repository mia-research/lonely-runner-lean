r"""
hp_isolation_v1 -- the ISOLATION LEMMA and its exact test.

LEMMA (isolation).  Let y0 be a breakpoint of the normal-form grid at which exactly
ONE runner rho increments, i.e. M_rho -> M_rho + 1 (mod 4) and the other three are
unchanged.  Then O cannot hold on both sides of y0.
PROOF.  Suppose nu is a permutation on the left.  Only coordinate rho changes, and it
changes to a DIFFERENT value (m -> m+1 mod 4 has no fixed point, and XOR with mu(rho)
is a bijection).  The other three coordinates still carry three distinct values, and
nu_rho was the missing fourth; so the new value of nu_rho equals one of the other
three.  The tuple is no longer injective.  QED

COROLLARY.  If the four speeds are PAIRWISE COPRIME then the only breakpoint of the
grid at which two runners increment simultaneously is y = 0, so no two adjacent cells
are both in O:  the O-cells are isolated, and #O-cells <= ceil(K/2) with K the number
of cells.

This script tests both statements exactly and reports, for double breakpoints, whether
O can survive (it can: the two changed coordinates may swap).
"""
import itertools, sys
from math import lcm, gcd
from fractions import Fraction as F

R4 = (1, 3, 5, 7)
MU = (0, 1, 2, 3)


def cells(sp):
    D = lcm(*sp)
    pts = {}
    for e in sp:
        for a in range(0, D, D // e):
            pts.setdefault(a, set()).add(e)
    p = sorted(pts)
    p2 = p + [D]
    out = []
    for i in range(len(p)):
        a = p2[i]
        nu = tuple((((e * a) // D) % 4) ^ m for e, m in zip(sp, MU))
        out.append((a, p2[i + 1], len(set(nu)) == 4, pts[a]))
    return out, D


print("isolation test: adjacent cells both in O, split by how many runners increment")
print(f"{'tuple':>20} {'pairwise coprime':>17} {'cells':>6} {'O-cells':>8} "
      f"{'adj pairs (simple bp)':>22} {'adj pairs (multi bp)':>21}")
tests = [(1,3,5,7),(1,11,5,7),(17,3,5,7),(9,3,21,15),(1,3,13,15),(1,19,21,39),
         (1,11,13,23),(41,43,13,15),(9,19,37,47),(33,27,13,7),(25,35,5,15),(9,27,45,63)]
for sp in tests:
    cs, D = cells(sp)
    pc = all(gcd(sp[i], sp[j]) == 1 for i in range(4) for j in range(i + 1, 4))
    nO = sum(1 for c in cs if c[2])
    simple = multi = 0
    for i in range(len(cs) - 1):
        if cs[i][2] and cs[i + 1][2]:
            if len(cs[i + 1][3]) == 1:
                simple += 1
            else:
                multi += 1
    print(f"{str(sp):>20} {str(pc):>17} {len(cs):>6} {nO:>8} {simple:>22} {multi:>21}")

print("\nexhaustive sweep for a violation of the isolation lemma (simple breakpoints only)")
viol = 0; n = 0
for qs in itertools.product(range(6), repeat=4):
    sp = tuple(8 * q + r for q, r in zip(qs, R4))
    if len(set(sp)) != 4:
        continue
    n += 1
    cs, D = cells(sp)
    for i in range(len(cs) - 1):
        if cs[i][2] and cs[i + 1][2] and len(cs[i + 1][3]) == 1:
            viol += 1
print(f"   {n} tuples (q <= 5): violations = {viol}")
