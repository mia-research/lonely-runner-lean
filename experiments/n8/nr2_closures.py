r"""
nr2_closures  --  the proved sufficient conditions, verified, and their coverage.

L1  REDUCTION (already proved in NONREP_STATE_v1 sec.2): gcd(E_non) >= 3 closes the leaf.
L2  LEMMA P1:  o <= 1/4  =>  |S^c| <= 2o <= 1/2  =>  |S| >= 1/2  =>  the leaf closes
    (B-lemma: |B_m1 u B_m2| < 1/2).
L3  DISCREPANCY.  P a set periodic on R with period p and density delta, X a union of
    n disjoint intervals of [0,1):   | |X n P| - delta|X| |  <=  n delta(1-delta) p.
    With M = e_rho0 / 2 (rho0 in {2,6}) resp. e_rho0 / 4 (rho0 = 4):

      rho0 in {2,6}:  |S^c| <= 2|P_even n O| <= o + n_O / M
      rho0 = 4     :  |S^c| = |A n U| + 2|A' n O| <= (o+u)/2 + (n_U + 3 n_O)/(4M)

    so the leaf closes as soon as M exceeds an explicit threshold depending only on
    the four unit speeds.
L4  LRC(7) DROP.  If the largest speed of E exceeds 7 times the second largest, then
    LRC(8) holds for E outright.  (Proof in the report; uses only intLRC_7.)

This script (a) checks L3's inequality numerically on a sweep -- it is an algebra
check, the lemma itself is proved -- and (b) reports coverage.

Usage:  python3 nr2_closures.py QMAX
"""
import itertools, sys
from math import gcd
from fractions import Fraction as F
from nr2_core import (MASK, ALL, safe_measure, o_measure, u_measure,
                      O_components, V_components, components, P_sets,
                      inter_measure, merge)

QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 5
HALF = F(1, 2)


def U_components(unit_speeds):
    R = (1, 3, 5, 7)
    def pred(_R, st):
        c = 0
        for rho, t in zip(R, st):
            c |= MASK[(rho, t)]
        return c == ALL
    return components(unit_speeds, R, pred)


def A_sets(e4):
    A, Ap, App = [], [], []
    for j in range(e4):
        iv = (F(j, e4), F(j + 1, e4))
        r = j % 8
        (A if r in (1, 2, 5, 6) else Ap if r in (0, 7) else App).append(iv)
    return merge(A), merge(Ap), merge(App)


# --------------------------------------------------------- unit-tuple cache
cache = {}
def unitdata(sp4):
    if sp4 not in cache:
        Oc = merge(O_components(sp4)[0])
        Uc = merge(U_components(sp4)[0])
        o = sum(b - a for a, b in Oc)
        u = sum(b - a for a, b in Uc)
        cache[sp4] = (Oc, Uc, o, u, len(Oc), len(Uc))
    return cache[sp4]


# --------------------------------------------------------- L3 numerical check
print("L3 -- discrepancy inequality, checked against the exact intersections")
viol = 0
n = 0
for rho0 in (2, 4, 6):
    for qs in itertools.product(range(4), repeat=5):
        sp = tuple(8 * q + r for q, r in zip(qs, (1, 3, 5, 7, rho0)))
        if len(set(sp)) != 5:
            continue
        n += 1
        Oc, Uc, o, u, nO, nU = unitdata(sp[:4])
        e0 = sp[4]
        if rho0 in (2, 6):
            M = F(e0, 2)
            Pe, Po = P_sets(rho0, (e0 - rho0) // 8)
            lhs = inter_measure(Pe, Oc)
            if abs(lhs - o / 2) > F(nO, 2) * (F(2) / M) / 2:   # n * delta(1-delta) * p
                viol += 1
        else:
            M = F(e0, 4)
            A, Ap, App = A_sets(e0)
            if abs(inter_measure(A, Uc) - u / 2) > F(nU, 4) * (F(1) / M):
                viol += 1
            if abs(inter_measure(Ap, Oc) - o / 4) > F(nO) * F(3, 16) * (F(2) / M):
                viol += 1
print(f"   {n} tuples (q <= 3): discrepancy bound violated {viol} times")

# --------------------------------------------------------- coverage
print(f"\nCOVERAGE over primitive base tuples with q <= {QMAX}")
tot = {}
for rho0 in (2, 4, 6):
    rhos = (1, 3, 5, 7, rho0)
    n = nL2 = nL3 = nres = 0
    residual = []
    for qs in itertools.product(range(QMAX + 1), repeat=5):
        sp = tuple(8 * q + r for q, r in zip(qs, rhos))
        if len(set(sp)) != 5:
            continue
        g = 0
        for e in sp:
            g = gcd(g, e)
        if g != 1:
            continue
        n += 1
        Oc, Uc, o, u, nO, nU = unitdata(sp[:4])
        if o <= F(1, 4):
            nL2 += 1
            continue
        e0 = sp[4]
        if rho0 in (2, 6):
            M = F(e0, 2)
            closed = (o + F(nO) / M) < HALF
        else:
            M = F(e0, 4)
            closed = ((o + u) / 2 + F(nU + 3 * nO, 4) / M) < HALF
        if closed:
            nL3 += 1
        else:
            nres += 1
            residual.append(sp)
    tot[rho0] = (n, nL2, nL3, nres, residual)
    print(f"   rho0={rho0}: primitive tuples {n}")
    print(f"      closed by L2 (o <= 1/4)      : {nL2}  ({100*nL2/n:.2f}%)")
    print(f"      closed by L3 (M above bound) : {nL3}  ({100*nL3/n:.2f}%)")
    print(f"      RESIDUAL                     : {nres}  ({100*nres/n:.2f}%)")
    if residual:
        print(f"      first residual tuples: {residual[:6]}")
    sys.stdout.flush()

# --------------------------------------------------------- L4 firing rate
print("\nL4 -- LRC(7) drop: largest speed of E > 7 * (second largest)")
fire = 0
tot4 = 0
for rho0 in (2, 4, 6):
    for qs in itertools.product(range(4), repeat=5):
        base = tuple(8 * q + r for q, r in zip(qs, (1, 3, 5, 7, rho0)))
        if len(set(base)) != 5:
            continue
        for m1 in range(1, 13):
            for m2 in range(m1 + 1, 13):
                E = sorted(set(base) | {8 * m1, 8 * m2})
                if len(E) != 7:
                    continue
                g = 0
                for e in E:
                    g = gcd(g, e)
                if g != 1:
                    continue
                tot4 += 1
                if E[-1] > 7 * E[-2]:
                    fire += 1
print(f"   {tot4} full tuples (base q <= 3, m <= 12): L4 fires {fire} times"
      f" ({100*fire/tot4:.2f}%)")
