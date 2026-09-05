#!/usr/bin/env python3
"""
m3_glv_control_forcing_v1.py

TESTS the claim that difference_set_xy_geometry_v1.py's "GLV-triple control
(must fire)" is ALGEBRAICALLY FORCED TO ZERO, not merely quiet.

Mechanism (the correctly-located version of the 1+w+w^2=0 identity):
  * S closed under the GLV endomorphism lam^(x,y) = (beta x, y), beta^3 = 1.
  * lam^ is a group endomorphism => the DIFFERENCE set D is also lam^-closed.
  * x(lam^ Q) = beta * x(Q), and x(-Q) = x(Q), so the multiset {x(Q) : Q in D}
    is closed under multiplication by beta.
  * M3 = sum_D chi3(x(Q)) groups into beta-orbits:
        chi3(x) + chi3(beta x) + chi3(beta^2 x) = chi3(x)*(1 + chi3(beta) + chi3(beta)^2)
  * chi3(beta) = beta^((p-1)/3).  For secp256k1, 9 does NOT divide p-1, so
    chi3(beta) is a PRIMITIVE cube root of unity => the bracket is 1+w+w^2 = 0.
  => M3 == 0 EXACTLY, for every lam^-closed set, with or without key structure.

Same for M3xy = sum chi3(x*y): y(lam^Q) = y(Q) so x*y -> beta*(x*y); and
chi3(-1) = 1 always (-1 is a cube), so the i<j sign convention is harmless.

EXACT ARITHMETIC (btc CLAUDE.md): chi3 values live in Z[w] as integer pairs
(a + b w),  w^2 = -1 - w.  A sum is zero iff the integer pair is (0,0).
No float anywhere in the verdict path.
"""
import random, sys

sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from ecc_secp256k1 import P as FP, N_ORDER, scalar_mul

CB = (FP - 1) // 3


# ---------------- exact Z[w] arithmetic: (a, b) = a + b*w, w^2 = -1 - w
ZERO = (0, 0)
ONE = (1, 0)
W = (0, 1)
W2 = (-1, -1)


def zadd(u, v):
    return (u[0] + v[0], u[1] + v[1])


def chi3_exact(a):
    """Cubic character as an EXACT element of Z[w]; 0 for a == 0.

    Mirrors difference_set_xy_geometry_v1.chi3's convention: the numerically
    smaller of the two nontrivial cube roots of unity in F_p maps to w.
    (Any fixed bijection {1,rho,rho^2} -> {1,w,w^2} is a genuine character,
    which is all the forcing argument needs.)
    """
    a %= FP
    if a == 0:
        return ZERO
    r = pow(a, CB, FP)
    if r == 1:
        return ONE
    r2 = pow(r, 2, FP)
    return W if r < r2 else W2


# ---------------- curve helpers (affine, exact ints)
def add_affine(A, B):
    if A is None:
        return B
    if B is None:
        return A
    x1, y1 = A
    x2, y2 = B
    if x1 == x2:
        if (y1 + y2) % FP == 0:
            return None
        m = (3 * x1 * x1) * pow(2 * y1, -1, FP) % FP
    else:
        m = (y2 - y1) * pow(x2 - x1, -1, FP) % FP
    x3 = (m * m - x1 - x2) % FP
    return x3, (m * (x1 - x3) - y1) % FP


def neg(A):
    return (A[0], (-A[1]) % FP)


def m3_exact(points, pairs):
    """Exact (M3, M3xy) in Z[w] over the given index pairs."""
    M3, M3xy = ZERO, ZERO
    cnt = 0
    for i, j in pairs:
        d = add_affine(points[i], neg(points[j]))
        if d is None:
            continue
        xd, yd = d
        M3 = zadd(M3, chi3_exact(xd))
        M3xy = zadd(M3xy, chi3_exact((xd * yd) % FP))
        cnt += 1
    return M3, M3xy, cnt


def all_pairs(n):
    return [(i, j) for i in range(n) for j in range(i + 1, n)]


def main():
    random.seed(20260730)

    # beta / lambda as the script itself derives them
    lam = pow(2, (N_ORDER - 1) // 3, N_ORDER)
    if pow(lam, 3, N_ORDER) != 1:
        lam = [l for l in range(2, 10000) if pow(l, 3, N_ORDER) == 1 and l != 1][0]

    chi3_beta_is_trivial = (pow(pow(3, (FP - 1) // 3, FP), CB, FP) == 1)
    print("=" * 76)
    print("Is the GLV-triple control FORCED, or just quiet?")
    print("=" * 76)
    print(f"  9 | (p-1) ?            {(FP-1) % 9 == 0}   ((p-1) mod 9 = {(FP-1)%9})")
    print(f"  chi3(beta) trivial ?   {chi3_beta_is_trivial}")
    print(f"  => predicted M3 on a lam-closed set: "
          f"{'AMPLIFIED x3' if chi3_beta_is_trivial else 'EXACTLY ZERO'}")

    SZ = 60  # 20 full lambda-triples; all pairs, no subsampling

    # ---- GLV-triple set (the control), fully lambda-closed
    glv = []
    for _ in range(SZ // 3):
        dd = random.randrange(1, N_ORDER)
        glv += [scalar_mul(dd),
                scalar_mul(dd * lam % N_ORDER),
                scalar_mul(dd * lam * lam % N_ORDER)]

    # ---- random control (not lambda-closed)
    rnd = [scalar_mul(random.randrange(1, N_ORDER)) for _ in range(SZ)]

    # ---- AP control
    d0 = random.randrange(1, N_ORDER)
    delta = random.randrange(1, 1 << 40)
    ap = [scalar_mul((d0 + i * delta) % N_ORDER) for i in range(SZ)]

    print(f"\n  ALL {len(all_pairs(SZ))} pairs of a {SZ}-point set, exact Z[w] sums:")
    print(f"  {'set':<26} {'M3 (exact)':>16} {'M3xy (exact)':>16}  zero?")
    for name, pts in (("GLV-triple (lam-closed)", glv),
                      ("random-curve", rnd),
                      ("AP", ap)):
        M3, M3xy, cnt = m3_exact(pts, all_pairs(SZ))
        z = (M3 == ZERO and M3xy == ZERO)
        print(f"  {name:<26} {str(M3):>16} {str(M3xy):>16}  {z}")

    # ---- the subsampling residual: what the shipped script actually reports
    print("\n  Effect of the shipped script's maxpairs subsampling on the GLV control:")
    print("  (|M3| is suppressed toward 0 in proportion to the pairs RETAINED,")
    print("   so the control reads 'weak', not 'broken'.)")
    ap_all = all_pairs(SZ)
    for frac in (100, 94, 75, 50):
        k = len(ap_all) * frac // 100
        sub = random.sample(ap_all, k)
        M3, M3xy, cnt = m3_exact(glv, sub)
        # descriptive magnitude only (never a verdict): exact norm in Z[w]
        a, b = M3
        norm2 = a * a - a * b + b * b
        print(f"    keep {frac:3d}% of pairs ({k:5d}): M3={str(M3):>14}  "
              f"|M3|^2={norm2:<8} |M3|/sqrt(n) ~ {(norm2/cnt) ** 0.5:.3f}")


if __name__ == "__main__":
    main()
