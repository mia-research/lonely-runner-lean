r"""
nr2_reflection  --  the reflection x -> 1-x, and the EXACT criterion it produces.

REFLECTION.  For x not a breakpoint, floor(e(1-x)) = e - 1 - floor(e x), so the state
t_e goes to rho - 1 - t_e (mod 8) and

    bad(rho, rho - 1 - t)  =  - bad(rho, t) - 1     (verified exhaustively below),

hence cov(1-x) = -cov(x) - 1.  Since r -> -r-1 exchanges the odd and the even residues
of Z/8, the reflection exchanges

    O = {units cover all 4 ODD residues}   <->   V = {units cover all 4 EVEN residues},

so o = v.  It fixes U = O n V and the blocked set, and on the rho0 side it sends
t0 -> rho0 - 1 - t0, which exchanges the two halves of the rho0 partition:

    rho0 in {2,6}:  P_even <-> P_odd
    rho0 = 4     :  A' <-> A'' ,  A -> A .

CONSEQUENCES (exact, no measure estimate):

  rho0 = 4      :   |S^c|  =  |A n U|  +  2 |A' n O|          (an IDENTITY)
                    so    |S| >= 1/2   <=>   2|A' n O| + |A n U| <= 1/2 .
  rho0 in {2,6} :   |S^c|  <=  2 |P_even n O|  .

Both are checked here against the direct cell computation, exactly.
"""
import itertools, sys
from math import gcd
from fractions import Fraction as F
from nr2_core import (BADSET, MASK, OMASK, EMASK, ALL, ODD, EVEN, safe_measure,
                      o_measure, v_measure, u_measure, O_components, V_components,
                      components, P_sets, inter_measure, merge, cell_table)

# ---------------------------------------------------------------- (R0)
print("(R0) bad(rho, rho-1-t) == -bad(rho,t)-1  for all rho in 1..7, t in Z/8:")
ok = all(BADSET[(rho, (rho - 1 - t) % 8)] ==
         frozenset((-a - 1) % 8 for a in BADSET[(rho, t)])
         for rho in range(1, 8) for t in range(8))
print(f"     {ok}")
print("     r -> -r-1 exchanges odds and evens:",
      sorted((-r - 1) % 8 for r in (1, 3, 5, 7)) == [0, 2, 4, 6])

# ---------------------------------------------------------------- (R1)
print("\n(R1) o == v on every unit tuple in the sweep")
bad = 0
n = 0
for qs in itertools.product(range(6), repeat=4):
    sp = tuple(8 * q + r for q, r in zip(qs, (1, 3, 5, 7)))
    if len(set(sp)) != 4:
        continue
    n += 1
    if o_measure(sp) != v_measure(sp):
        bad += 1
print(f"     {n} unit tuples (q <= 5), o != v in {bad}")

# ------------------------------------------------- A / A' / A'' for rho0 = 4
def A_sets(e4):
    """(A, A', A'') as merged interval lists;  A: t mod 8 in {1,2,5,6} (bad empty),
       A': {0,7} (bad = evens),  A'': {3,4} (bad = odds)."""
    A, Ap, App = [], [], []
    for j in range(e4):
        iv = (F(j, e4), F(j + 1, e4))
        r = j % 8
        (A if r in (1, 2, 5, 6) else Ap if r in (0, 7) else App).append(iv)
    return merge(A), merge(Ap), merge(App)


def U_components(unit_speeds):
    R = (1, 3, 5, 7)
    def pred(_R, st):
        c = 0
        for rho, t in zip(R, st):
            c |= MASK[(rho, t)]
        return c == ALL
    return components(unit_speeds, R, pred)


print("\n(R2) rho0 = 4:  |S^c| == |A n U| + 2 |A' n O|   (exact identity)")
bad = 0; n = 0; worst = None
for qs in itertools.product(range(5), repeat=5):
    sp = tuple(8 * q + r for q, r in zip(qs, (1, 3, 5, 7, 4)))
    if len(set(sp)) != 5:
        continue
    n += 1
    sc = 1 - safe_measure(sp, (1, 3, 5, 7, 4))
    A, Ap, App = A_sets(sp[4])
    Oc = merge(O_components(sp[:4])[0])
    Vc = merge(V_components(sp[:4])[0])
    Uc = merge(U_components(sp[:4])[0])
    lhs = inter_measure(A, Uc) + 2 * inter_measure(Ap, Oc)
    if lhs != sc:
        bad += 1
        if bad <= 3:
            print("     MISMATCH", sp, sc, lhs)
    # also the pairwise reflection identity |A' n O| == |A'' n V|
    if inter_measure(Ap, Oc) != inter_measure(App, Vc):
        print("     REFLECTION MISMATCH", sp)
    if worst is None or sc > worst[0]:
        worst = (sc, sp)
print(f"     {n} tuples (q <= 4), identity fails in {bad}")
print(f"     max |S^c| over them: {worst[0]} = {float(worst[0]):.6f} at {worst[1]}")

print("\n(R3) rho0 in {2,6}:  |S^c| <= 2 |P_even n O|,  and |P_even n O| == |P_odd n V|")
for rho0 in (2, 6):
    bad = 0; refl_bad = 0; n = 0; tight = 0
    for qs in itertools.product(range(5), repeat=5):
        sp = tuple(8 * q + r for q, r in zip(qs, (1, 3, 5, 7, rho0)))
        if len(set(sp)) != 5:
            continue
        n += 1
        sc = 1 - safe_measure(sp, (1, 3, 5, 7, rho0))
        Pe, Po = P_sets(rho0, (sp[4] - rho0) // 8)
        Oc = merge(O_components(sp[:4])[0])
        Vc = merge(V_components(sp[:4])[0])
        a, b = inter_measure(Pe, Oc), inter_measure(Po, Vc)
        if a != b:
            refl_bad += 1
        if sc > a + b:
            bad += 1
        if sc == a + b:
            tight += 1
    print(f"     rho0={rho0}: {n} tuples, bound violated {bad} times,"
          f" reflection identity fails {refl_bad} times, bound tight {tight} times")
