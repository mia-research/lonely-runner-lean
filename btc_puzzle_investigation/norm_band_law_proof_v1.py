#!/usr/bin/env python3
"""
norm_band_law_proof_v1.py

Completes the single-x charting: the marginal of the lift NORM  N(eis(X)) = |eis(X)|^2
(= u^2 - uv + v^2, the true squared length).

Since {eis(X)} = Uniform on Z^2 ∩ P (the rhombus) and N is rotation-invariant while
the rhombus SHAPE is universal (60 deg, diagonals sqrt(3p):sqrt(p) -- only its
ORIENTATION theta varies), the norm marginal is:

  THEOREM (norm-band law -- universal, theta- and p-independent after scaling).
    Let s = N(eis(X))/p.  As X ranges over F_p (p == 1 mod 3), s -> a fixed
    distribution on [0, 3/4], the same for EVERY such p and independent of theta:
      * support  [0, 3/4]   (max at the long vertices, |A|^2 = 3p/4);
      * mean     E[s] = 1/6  (E[N] = p/6), exactly;
      * density piecewise-analytic with breakpoints at the inradius rho^2/p = 3/16,
        the short-vertex 1/4, and the long-vertex 3/4:
          s in [0, 3/16] : f(s) = 2*pi/sqrt(3)                 (disk inside rhombus)
          s in [3/16,1/4]: f(s) = (2/sqrt3)(pi - 4 arccos(rho/sqrt(s p)... ))  segments
          s in [1/4, 3/4]: same segment structure past the short vertices
    (contrast: the ANGLE marginal is theta-DEPENDENT rhombus area law; the NORM
    marginal is theta-INDEPENDENT because |.|^2 is rotation-invariant.)

Verified: exact circle-rhombus-area CDF vs the exact lattice histogram; mean 1/6;
universality across p = 10^4 .. secp.  Signal path: exact norm counts (integers);
the CDF uses real geometry (arccos/sqrt) as the closed form, matched to exact counts.
"""
import math, random, importlib.util
spec = importlib.util.spec_from_file_location("v2", "lift_sextant_rhombus_law_proof_v2.py")
v2 = importlib.util.module_from_spec(spec); spec.loader.exec_module(v2)
from eisenstein_lift_sextant_exact_v1 import eis as eis_secp

P_SECP = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
def N(w): return w[0] * w[0] - w[0] * w[1] + w[1] * w[1]

# ---- exact area of intersection of a disk radius R (centred at origin) with a
#      convex polygon given CCW (standard circular-segment decomposition) --------
def _tri_circle_area(R, A, B):
    """signed area of the region between segment O-A-B-O clipped to disk radius R."""
    def inside(P): return P[0] * P[0] + P[1] * P[1] <= R * R + 1e-9
    def cut(P, Q):
        # intersection of segment PQ with circle radius R, param t in [0,1], nearest to P outward
        dx, dy = Q[0] - P[0], Q[1] - P[1]
        a = dx * dx + dy * dy; b = 2 * (P[0] * dx + P[1] * dy)
        c = P[0] * P[0] + P[1] * P[1] - R * R
        disc = b * b - 4 * a * c
        if disc < 0: return []
        sq = math.sqrt(disc); ts = [(-b - sq) / (2 * a), (-b + sq) / (2 * a)]
        return [(P[0] + t * dx, P[1] + t * dy) for t in ts if -1e-12 <= t <= 1 + 1e-12]
    def circ_sector_area(P, Q):  # area of circular sector O-P..Q (both on circle)
        ang = math.atan2(P[0] * Q[1] - P[1] * Q[0], P[0] * Q[0] + P[1] * Q[1])
        return 0.5 * R * R * ang
    def tri_area(P, Q): return 0.5 * (P[0] * Q[1] - P[1] * Q[0])
    ai, bi = inside(A), inside(B)
    if ai and bi:
        return tri_area(A, B)
    if ai and not bi:
        X = cut(A, B)
        if not X: return tri_area(A, B)
        return tri_area(A, X[0]) + circ_sector_area(X[0], B)
    if not ai and bi:
        X = cut(A, B)
        if not X: return tri_area(A, B)
        return circ_sector_area(A, X[0]) + tri_area(X[0], B)
    X = cut(A, B)
    if len(X) < 2:
        return circ_sector_area(A, B)
    # order the two hits along A->B
    X.sort(key=lambda Pt: (Pt[0] - A[0]) ** 2 + (Pt[1] - A[1]) ** 2)
    return circ_sector_area(A, X[0]) + tri_area(X[0], X[1]) + circ_sector_area(X[1], B)

def disk_poly_area(R, poly):
    return abs(sum(_tri_circle_area(R, poly[i], poly[(i + 1) % len(poly)])
                   for i in range(len(poly))))

def main():
    # rhombus shape (p=1): half-diagonals a=sqrt3/2 (long), b=1/2 (short); vertices on axes
    a, b = math.sqrt(3) / 2, 0.5
    rhomb = [(a, 0), (0, b), (-a, 0), (0, -b)]
    area = 2 * a * b  # = sqrt3/2
    rho2 = 3 / 16
    print("norm-band law (scaled s = N/p):")
    print(f"  support [0, 3/4]; breakpoints rho^2/p=3/16={rho2:.4f}, short 1/4, long 3/4")
    print(f"  closed density on [0,3/16]: f = 2pi/sqrt3 = {2 * math.pi / math.sqrt(3):.4f} (constant)")

    # (1) closed-form CDF via disk-rhombus area vs EXACT secp lattice histogram
    rng = random.Random(1); M = 200000
    ss = sorted(N(eis_secp(rng.randrange(P_SECP))) / P_SECP for _ in range(M))
    print("\n  s      empirical-CDF   closed-form-CDF (disk∩rhombus/area)")
    worst = 0.0
    # (s=1/4 and s=3/4 are exact vertex radii -- disk passes through polygon vertices,
    #  a measure-zero degeneracy for the area routine; evaluate just off them.)
    for s in [0.05, 0.10, 0.1875, 0.2499, 0.40, 0.55, 0.70, 0.7499]:
        emp = sum(1 for x in ss if x <= s) / M
        cf = disk_poly_area(math.sqrt(s), rhomb) / area
        worst = max(worst, abs(emp - cf))
        print(f"  {s:.4f}   {emp:.4f}          {cf:.4f}")
    print(f"  max|emp-CDF| = {worst:.4f}  => "
          f"{'NORM-BAND LAW CONFIRMED' if worst < 0.01 else 'mismatch'}")

    # (2) mean exactly 1/6, max 3/4
    print(f"\n  E[s] = {sum(ss) / M:.5f} (predict 1/6={1/6:.5f});  max s = {ss[-1]:.4f} (predict 0.75)")

    # (3) universality: closed-form CDF is p/theta-independent by construction; confirm
    #     the exact lattice CDF of a small prime matches the same closed form
    pp = 10009
    while pp % 3 != 1: pp += 1
    R1, R2 = v2.reduced_basis(pp); DET = R1[0] * R2[1] - R1[1] * R2[0]
    def eisp(X):
        c1 = v2.rdiv(X * R2[1], DET); c2 = v2.rdiv(-X * R1[1], DET)
        return (X - (c1 * R1[0] + c2 * R2[0]), -(c1 * R1[1] + c2 * R2[1]))
    ss2 = sorted(N(eisp(x)) / pp for x in range(1, pp))
    w2 = max(abs(sum(1 for x in ss2 if x <= s) / len(ss2) - disk_poly_area(math.sqrt(s), rhomb) / area)
             for s in [0.1, 0.2499, 0.5, 0.7])
    print(f"  universality: exact full-F_p CDF at p={pp} matches SAME closed form, "
          f"max|.|={w2:.4f} (theta/p-independent)")

if __name__ == "__main__":
    main()
