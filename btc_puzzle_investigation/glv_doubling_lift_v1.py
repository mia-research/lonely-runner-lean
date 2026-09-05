#!/usr/bin/env python3
"""
glv_doubling_lift_v1.py

Direction (1) opener: reach from the UNIT action (mu6, clean 2-point law) toward the
SCALAR / group law. The doubling map on x-coordinates,
    phi2(x) = (x^4 - 56 x) / (4 (x^3 + 7))   mod p,
is a SCALAR operation (P -> 2P, i.e. d -> 2d) computable with x only (no y, no DLP).
Like S3 it is [omega]-covariant:  phi2(beta x) = beta phi2(x)  (verified exactly).

Question: does a scalar operation leave a lift-geometric signature? We measure the joint
(sextant(eis x), sextant(eis phi2 x)) vs a matched shuffle null, and test the mu3-covariance
the [omega]-symmetry forces (rotating x by beta shifts BOTH sextants together). Exact
integers in the arithmetic path; MI is a statistic ranked against a matched permutation null.

Note on moduli (the amicable bridge): the lift reduces mod pi_p; the group law / scalars
live in E(F_p) ~ Z[omega]/(pi_p - 1) = Z[omega]/pi_n. Lift<->scalar crosses pi_p <-> pi_n,
the amicable shift. This probe is the first x-only step across it.
"""
import random
import math
from glv_fundamental_domain_law_v1 import make_lift, sextant, cube_roots, P_SECP, AP_SECP, BP_SECP
from lift_sextant_rhombus_law_proof_v2 import gauss_reduce, sector_props
from fractions import Fraction as F


def phi2(x, p):
    """x-coordinate of 2P for y^2 = x^3 + 7 (x-only doubling map)."""
    den = (4 * (pow(x, 3, p) + 7)) % p
    if den == 0:
        return None
    return ((pow(x, 4, p) - 56 * x) * pow(den, p - 2, p)) % p


def mi_bits(joint):
    tot = sum(sum(r) for r in joint)
    if tot == 0:
        return 0.0
    rs = [sum(r) for r in joint]
    cs = [sum(joint[i][j] for i in range(len(joint))) for j in range(len(joint[0]))]
    mi = 0.0
    for i in range(len(joint)):
        for j in range(len(joint[0])):
            c = joint[i][j]
            if c and rs[i] and cs[j]:
                mi += (c / tot) * math.log2((c * tot) / (rs[i] * cs[j]))
    return mi


def run(name, p, Xs, R1=None, R2=None):
    R1, R2, DET, reduce_P, eis = make_lift(p, R1, R2)
    b1, b2 = cube_roots(p)
    # verify [omega]-covariance of phi2 for both cube roots (exact)
    cov = all(phi2((b * x) % p, p) == (b * phi2(x, p)) % p
              for b in (b1, b2) for x in Xs[:30] if phi2(x, p) and phi2((b * x) % p, p))

    joint = [[0] * 6 for _ in range(6)]
    for x in Xs:
        y = phi2(x, p)
        if y is None or y == 0 or x == 0:
            continue
        joint[sextant(*eis(x))][sextant(*eis(y))] += 1
    M = sum(sum(r) for r in joint)

    # mu3-covariance test: simultaneous +2 shift of both indices should preserve the table
    shift = [[joint[(i - 2) % 6][(j - 2) % 6] for j in range(6)] for i in range(6)]
    mu3_sym = (joint == shift)

    # MI vs matched shuffle null
    obs = mi_bits(joint)
    rng = random.Random(7)
    xs = [sextant(*eis(x)) for x in Xs if phi2(x, p) not in (None, 0) and x != 0]
    ys = [sextant(*eis(phi2(x, p))) for x in Xs if phi2(x, p) not in (None, 0) and x != 0]
    nulls = []
    for _ in range(200):
        yp = ys[:]; rng.shuffle(yp)
        jn = [[0] * 6 for _ in range(6)]
        for a, b in zip(xs, yp):
            jn[a][b] += 1
        nulls.append(mi_bits(jn))
    mu = sum(nulls) / len(nulls)
    sd = (sum((v - mu) ** 2 for v in nulls) / len(nulls)) ** 0.5
    z = (obs - mu) / sd if sd else 0.0

    props = sector_props(R1, R2)
    pinned = [t for t in range(6) if props[t] == F(1, 8)]
    print(f"\n=== {name} (M={M}) ===")
    print(f"    phi2 [omega]-covariant (phi2(bx)=b.phi2(x)): {cov}")
    print(f"    joint (sextant x) x (sextant 2x):")
    for i in range(6):
        tag = " <-pin" if i in pinned else "      "
        print(f"      x-sext {i}{tag}: {joint[i]}")
    print(f"    mu3-covariance (simultaneous +2 shift invariance of the table): {mu3_sym}")
    print(f"    MI = {obs:.5f} bits   null {mu:.5f}+-{sd:.5f}   z = {z:+.1f}   "
          f"({'STRUCTURE beyond mu3-symmetry' if z > 4 else 'at matched-null floor'})")


def main():
    print("=" * 70)
    print("Doubling map phi2 (scalar x2) on the Eisenstein lift -- direction (1) opener")
    print("=" * 70)
    for p in (1009, 100003):
        run(f"full F_p p={p}", p, list(range(1, p)))
    rng = random.Random(999)
    Xs = [rng.randrange(1, P_SECP) for _ in range(60000)]
    R1s, R2s = gauss_reduce((AP_SECP, BP_SECP), (-BP_SECP, AP_SECP - BP_SECP))
    run("secp uniform-X", P_SECP, Xs, R1=R1s, R2=R2s)


if __name__ == "__main__":
    main()
