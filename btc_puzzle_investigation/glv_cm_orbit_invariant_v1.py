#!/usr/bin/env python3
"""
glv_cm_orbit_invariant_v1.py

Digesting our own structure: the mu3-orbit cocycle  omega c0 + omega^2 c1 + c2 = 0  (verified)
with c_i in {0,+-R} FORCES (Z-basis {1,omega} argument) c0 = c1 = c2. I.e. the CM correction
is CONSTANT along the whole period-3 orbit {X, bX, b^2 X}: a single label eps in {0,+,-}.

This upgrades "corrections sum to zero" to "correction is a mu3-ORBIT INVARIANT" (a class
function on orbit space F_p^* / mu3, of size (p-1)/3). We verify, exactly:

  (T1) c0 == c1 == c2 as VECTORS, every orbit (the sharp form).
  (T2) label distribution over orbits = 3/4 : 1/8 : 1/8  (eps=0 : +R : -R).
  (T3) eps=0  <=>  eis(X) in the mu3-core  <=>  the three lifts are EXACT omega-rotations of
       one another (a perfect equilateral / mu3-symmetric triple). So a "pure" orbit lifts to
       a rigid triangle; a "flap" orbit's triangle is closed by a constant shift eps*R.

Exact integers throughout (label fractions exact on full F_p).
"""
from fractions import Fraction as F
from glv_fundamental_domain_law_v1 import make_lift, sextant, cube_roots, P_SECP, AP_SECP, BP_SECP
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce, enorm


def om(w):
    u, v = w
    return (-v, u - v)


def om2(w):
    u, v = w
    return (v - u, -u)


def analyze(name, p, Xs, R1=None, R2=None, full=False):
    R1, R2, DET, reduce_P, eis = make_lift(p, R1, R2)
    b1, b2 = cube_roots(p)
    # pick beta whose matching zeta is omega^2 (eis(bX) = reduce_P(om2(eis X)))
    probe = [x for x in Xs[:20] if x % p]
    beta = b1 if all(eis((b1 * x) % p) == reduce_P(*om2(eis(x))) for x in probe) else b2

    seen = set()
    n_orbits = 0
    label = {0: 0, 1: 0, -1: 0}
    t1_ok = 0                       # c0==c1==c2
    t3_core = 0                     # eps==0  <=> lifts are exact omega-rotations
    eps_of_core = {True: {0: 0, 1: 0, -1: 0}, False: {0: 0, 1: 0, -1: 0}}
    for X in Xs:
        if X % p == 0 or X in seen:
            continue
        orb = [X, (beta * X) % p, (beta * beta * X) % p]
        for o in orb:
            seen.add(o)
        n_orbits += 1
        U = [eis(o) for o in orb]
        c = [(U[(i + 1) % 3][0] - om2(U[i])[0], U[(i + 1) % 3][1] - om2(U[i])[1]) for i in range(3)]
        if c[0] == c[1] == c[2]:
            t1_ok += 1
        # label from c0 (as multiple of a basis vector; 0, +/-R1, +/-R2)
        cv = c[0]
        eps = 0
        if cv != (0, 0):
            eps = 1 if (cv == tuple(R1) or cv == tuple(R2)) else -1
        label[eps] += 1
        # T3: eps==0 iff the triple is an exact omega-rotation set (rigid equilateral)
        rigid = (U[1] == om2(U[0]) and U[2] == om2(U[1]))
        if rigid == (c[0] == (0, 0)):
            t3_core += 1
        eps_of_core[rigid][eps] += 1

    tot = n_orbits
    print(f"\n=== {name}  ({tot} orbits, {'full F_p' if full else 'sampled'}) ===")
    print(f"  (T1) c0==c1==c2 (correction constant on orbit): {t1_ok}/{tot} "
          f"{'ALL' if t1_ok == tot else 'FAIL'}")
    fr = {k: F(label[k], tot) for k in label}
    print(f"  (T2) orbit-label distribution: eps=0:{label[0]} ({float(fr[0]):.4f})  "
          f"+R:{label[1]} ({float(fr[1]):.4f})  -R:{label[-1]} ({float(fr[-1]):.4f})")
    print(f"        predicted 3/4 : 1/8 : 1/8  -> "
          f"{'MATCH' if full and fr[0]==F(3,4) else f'~ ({float(fr[0]):.3f},{float(fr[1]):.3f},{float(fr[-1]):.3f})'}")
    print(f"  (T3) eps=0 <=> rigid omega-triangle: {t3_core}/{tot} "
          f"{'ALL' if t3_core == tot else 'FAIL'}   "
          f"(rigid&eps0={eps_of_core[True][0]}, nonrigid&epsnonzero="
          f"{eps_of_core[False][1]+eps_of_core[False][-1]})")


def main():
    print("=" * 72)
    print("CM correction is a mu3-ORBIT INVARIANT (constant along {X, bX, b^2 X})")
    print("=" * 72)
    for p in (10009, 100003):
        analyze(f"full F_p p={p}", p, list(range(1, p)), full=True)
    import random
    rng = random.Random(7)
    Xs = [rng.randrange(1, P_SECP) for _ in range(45000)]
    R1s, R2s = gauss_reduce((AP_SECP, BP_SECP), (-BP_SECP, AP_SECP - BP_SECP))
    analyze("secp sampled", P_SECP, Xs, R1=R1s, R2=R2s)


if __name__ == "__main__":
    main()
