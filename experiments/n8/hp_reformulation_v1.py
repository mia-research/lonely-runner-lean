r"""
hp_reformulation_v1 -- VERIFY, exactly, the three structural identities that turn
o, v, u into Weyl box-averages of a closed geodesic on T^4.

(T1)  SHIFT IDENTITY.  For a unit speed e = 8q+rho,  bad(rho, t+e) = bad(rho,t) - 1
      (as subsets of Z/8).  The shift is the SAME (-1) for every unit rho.
      Consequences: U(x+1) = U(x);  O(x+1) = V(x);  V(x+1) = O(x);  O(x+2) = O(x).

(T2)  QUADRANT / OCTANT REFORMULATION.  Put theta = x/8.  Then
          m_rho(x) := floor(e_rho x / 2) mod 4  =  floor(4 * frac(e_rho theta))
          t_rho(x) := floor(e_rho x)     mod 8  =  floor(8 * frac(e_rho theta))
      O  = { theta : (m_rho XOR mu(rho))_rho  is a permutation of {0,1,2,3} },
      mu(1),mu(3),mu(5),mu(7) = 0,1,2,3.
      U  = O and (the four even blocks distinct), a union of octant boxes.
      o = |O| and u = |U| as measures in theta on [0,1).

(T3)  PAIR CORRELATION.  <sq(a.)sq(b.)> = gcd(a,b)^2/(ab) if v2(a)=v2(b), else 0.

Everything below is exact Fraction arithmetic.  Cells are evaluated at their ENTRY
point and the breakpoint list is audited for completeness (requirement (i)).
"""
import itertools, sys
from math import lcm, gcd
from fractions import Fraction as F
from nr2_core import BADSET, MASK, OMASK, EMASK, ALL, ODD, EVEN, o_measure, u_measure, v_measure

R4 = (1, 3, 5, 7)
MU = {1: 0, 3: 1, 5: 2, 7: 3}

# ---------------------------------------------------------------- (T1)
print("(T1) shift identity  bad(rho, t+e) == bad(rho,t) - 1  for every unit e=8q+rho")
ok = True
for rho in R4:
    for q in range(4):
        e = 8 * q + rho
        for t in range(8):
            lhs = BADSET[(rho, (t + e) % 8)]
            rhs = frozenset((r - 1) % 8 for r in BADSET[(rho, t)])
            if lhs != rhs:
                ok = False
                print("   FAIL", rho, q, t, sorted(lhs), sorted(rhs))
print("   holds for all rho in {1,3,5,7}, q<4, t:", ok)

# also: for NON-unit rho the shift is NOT uniform (so T1 is a units-only statement)
nonuni = []
for rho in (2, 4, 6):
    for q in range(3):
        e = 8 * q + rho
        shifts = set()
        for t in range(8):
            L = BADSET[(rho, (t + e) % 8)]; B = BADSET[(rho, t)]
            shifts.add(frozenset((a - b) % 8 for a in L for b in B) if B else None)
        nonuni.append((rho, e, len(shifts)))
print("   (non-unit rho: shift is not a single translate)", nonuni[:4])

# ---------------------------------------------------------------- exact grids
def grid_measure(speeds, mult, pred):
    """measure of { theta in [0,1) : pred( tuple(floor(mult*frac(e*theta))) ) }.
    Breakpoints are j/(mult*e).  Entry evaluation.  Exact."""
    D = lcm(*[mult * e for e in speeds])
    pts = set()
    for e in speeds:
        step = D // (mult * e)
        pts.update(range(0, D, step))
    p = sorted(pts); p.append(D)
    tot = 0
    for i in range(len(p) - 1):
        a = p[i]
        st = tuple(((mult * e * a) // D) % mult for e in speeds)
        if pred(st):
            tot += p[i + 1] - a
    return F(tot, D), len(p) - 1, D, p


def grid_audit(speeds, mult):
    """requirement (i): for every cell [a,b) over D and every f = mult*e, check
       (1) no integer k with a/D < k/f < b/D, and
       (2) floor(f*a/D) == floor(f*b/D) - [f*b/D integral]."""
    D = lcm(*[mult * e for e in speeds])
    pts = set()
    for e in speeds:
        step = D // (mult * e)
        pts.update(range(0, D, step))
    p = sorted(pts); p.append(D)
    n_int = n_mis = 0
    for i in range(len(p) - 1):
        a, b = p[i], p[i + 1]
        for e in speeds:
            f = mult * e
            lo = (a * f) // D; hi = (b * f) // D
            for k in range(lo + 1, hi + 1):
                if a * f < k * D < b * f:
                    n_int += 1
            entry = (a * f) // D
            exit_ = (b * f) // D - (1 if (b * f) % D == 0 else 0)
            if entry != exit_:
                n_mis += 1
    return len(p) - 1, n_int, n_mis


def pred_O_quad(st):
    nu = tuple(m ^ MU[r] for m, r in zip(st, R4))
    return len(set(nu)) == 4


def pred_U_oct(st):
    """st = (t_rho) octants.  O and V both, i.e. the union of the four bad pairs is
    all of Z/8."""
    c = 0
    for rho, t in zip(R4, st):
        c |= MASK[(rho, t)]
    return c == ALL


def pred_O_oct(st):
    c = 0
    for rho, t in zip(R4, st):
        c |= OMASK[(rho, t)]
    return c == ODD


# ---------------------------------------------------------------- (T2)
print("\n(T2) quadrant/octant reformulation vs nr2_core")
print(f"{'tuple':>20} {'o (nr2)':>12} {'o (quad)':>12} {'u (nr2)':>12} {'u (oct)':>12} ok")
bad = 0
tests = [(1,3,5,7),(1,11,5,7),(17,3,5,7),(9,3,21,15),(1,3,13,15),(1,19,21,39),
         (25,35,5,15),(1,11,13,23),(33,27,13,7),(41,43,13,15)]
for sp in tests:
    o1 = o_measure(sp); u1 = u_measure(sp)
    o2, nc, _, _ = grid_measure(sp, 4, pred_O_quad)
    u2, nc2, _, _ = grid_measure(sp, 8, pred_U_oct)
    good = (o1 == o2 and u1 == u2)
    bad += (not good)
    print(f"{str(sp):>20} {str(o1):>12} {str(o2):>12} {str(u1):>12} {str(u2):>12} {good}")
print("   mismatches:", bad)

print("\n   boundary audit (requirement (i)) on the quadrant and octant grids:")
for sp in tests[:5]:
    for mult in (4, 8):
        nc, ni, nm = grid_audit(sp, mult)
        print(f"      {str(sp):>18} mult={mult}: cells={nc:6d} interior-breakpoints={ni} "
              f"entry!=exit={nm}")

# ---------------------------------------------------------------- periods
print("\n(T1) consequences checked on the octant grid (theta in [0,1) <-> x in [0,8))")
def shifted_measure(sp, pred, shift_x):
    """measure of { theta : pred(state at theta + shift_x/8) } -- shift by shift_x in x"""
    D = lcm(*[8 * e for e in sp]) 
    sh = F(shift_x, 8)
    pts = set()
    for e in sp:
        step = D // (8 * e)
        pts.update(range(0, D, step))
    p = sorted(pts); p.append(D)
    tot = 0
    for i in range(len(p) - 1):
        a = p[i]
        st = tuple(((8 * e * a) // D + shift_x * e) % 8 for e in sp)
        if pred(st):
            tot += p[i + 1] - a
    return F(tot, D)

for sp in tests[:6]:
    o = o_measure(sp); v = v_measure(sp); u = u_measure(sp)
    o_sh1 = shifted_measure(sp, pred_O_oct, 1)
    u_sh1 = shifted_measure(sp, pred_U_oct, 1)
    print(f"   {str(sp):>18} o={str(o):>12} v={str(v):>12} o==v:{o==v}"
          f"   |O(.+1)|={str(o_sh1):>12} ==v:{o_sh1==v}   |U(.+1)|==u:{u_sh1==u}")
