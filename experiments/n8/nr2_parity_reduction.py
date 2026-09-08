r"""
nr2_parity_reduction  --  the PARITY REDUCTION, verified two ways.

CLAIM (Lemma P).  Let E_non = {e_1,e_3,e_5,e_7,e_rho0}, e_rho = 8 q_rho + rho.
Write O (resp. V) for the set of x at which the FOUR UNIT runners already cover
every ODD (resp. every EVEN) residue of Z/8.  Split [0,1) by t0 = floor(e_rho0 x):

    rho0 in {2,6}:  P_odd  = { t0 mod 8 in {1,2,5,6} }   (bad(rho0,t0) is a pair of
                                                          ODD residues there)
                    P_even = { t0 mod 8 in {0,3,4,7} }    (a pair of EVEN residues)
    rho0 = 4     :  P_odd  = { t0 mod 8 in {3,4} }        (bad = all odds)
                    P_even = { t0 mod 8 not in {3,4} }    (bad = all evens, or empty)

Then                S^c  is contained in  (P_even n O) u (P_odd n V),
hence                |S^c|  <=  |P_even n O| + |P_odd n V|  <=  o + v = 2 o.

COROLLARY (Lemma P1).   o <= 1/4  ==>  |S| >= 1/2.

Part 1 of this script checks the containment CELL BY CELL (an exact statement about
the 8^5 possible entry states, so it is an exhaustive finite verification, not a
sample).  Part 2 checks the measure inequality on concrete tuples.
"""
import itertools, sys
from fractions import Fraction as F
from nr2_core import (MASK, OMASK, EMASK, ALL, ODD, EVEN, safe_measure,
                      o_measure, v_measure, P_sets, O_components, V_components,
                      inter_measure, merge)

# ---------------------------------------------------------------- Part 1
# state space: (t1,t3,t5,t7,t0) in (Z/8)^5.  Exhaustive.
print("PART 1 -- containment S^c  <=  (P_even n O) u (P_odd n V), on all 8^5 states")
for rho0 in (2, 4, 6):
    odd_t = {1, 2, 5, 6} if rho0 in (2, 6) else {3, 4}
    bad_states = 0
    viol = 0
    for st in itertools.product(range(8), repeat=5):
        cov = 0
        for rho, t in zip((1, 3, 5, 7, rho0), st):
            cov |= MASK[(rho, t)]
        if cov != ALL:
            continue
        bad_states += 1
        ucovO = ucovE = 0
        for rho, t in zip((1, 3, 5, 7), st[:4]):
            ucovO |= OMASK[(rho, t)]
            ucovE |= EMASK[(rho, t)]
        inO = (ucovO == ODD)
        inV = (ucovE == EVEN)
        t0 = st[4]
        ok = (inV if t0 % 8 in odd_t else inO)
        if not ok:
            viol += 1
            if viol <= 3:
                print("   VIOLATION", st)
    print(f"   rho0={rho0}: blocking states = {bad_states}, violations = {viol}")

# also record the parity type of bad(rho0,t0) to justify the split
print("\n   parity of bad(rho0,t) as a function of t mod 8:")
for rho0 in (2, 4, 6):
    row = []
    for t in range(8):
        s = [r for r in range(8) if (rho0 * r + t) % 8 in (0, 7)]
        row.append("odd" if s and all(r % 2 for r in s)
                   else "even" if s and all(r % 2 == 0 for r in s)
                   else "empty" if not s else "MIXED")
    print(f"     rho0={rho0}: " + " ".join(f"t={t}:{row[t]}" for t in range(8)))

# ---------------------------------------------------------------- Part 2
print("\nPART 2 -- measure inequality on concrete tuples (exact Fractions)")
CASES = []
for rho0 in (2, 4, 6):
    for qs in itertools.product(range(3), repeat=5):
        sp = tuple(8 * q + r for q, r in zip(qs, (1, 3, 5, 7, rho0)))
        if len(set(sp)) != 5:
            continue
        CASES.append((rho0, sp))
worst = None
nviol = 0
for rho0, sp in CASES:
    rhos = (1, 3, 5, 7, rho0)
    S = safe_measure(sp, rhos)
    Oc, _ = O_components(sp[:4])
    Vc, _ = V_components(sp[:4])
    Pe, Po = P_sets(rho0, (sp[4] - rho0) // 8)
    bnd = inter_measure(merge(Oc), Pe) + inter_measure(merge(Vc), Po)
    if 1 - S > bnd:
        nviol += 1
        print("   VIOLATION", sp, 1 - S, bnd)
    slack = bnd - (1 - S)
    if worst is None or slack < worst[0]:
        worst = (slack, sp, 1 - S, bnd)
print(f"   {len(CASES)} tuples (q <= 2), violations of |S^c| <= |Pe n O| + |Po n V| : {nviol}")
print(f"   tightest: slack {worst[0]} at {worst[1]}  (|S^c| = {worst[2]}, bound = {worst[3]})")

# ---------------------------------------------------------------- Part 3
print("\nPART 3 -- Lemma P1 in force: tuples with o <= 1/4 all have |S| >= 1/2")
n_ok = n_test = 0
for rho0, sp in CASES:
    o = o_measure(sp[:4])
    if o <= F(1, 4):
        n_test += 1
        if safe_measure(sp, (1, 3, 5, 7, rho0)) >= F(1, 2):
            n_ok += 1
print(f"   tuples with o <= 1/4 : {n_test};  of these |S| >= 1/2 : {n_ok}")
