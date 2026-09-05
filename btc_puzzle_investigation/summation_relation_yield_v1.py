#!/usr/bin/env python3
"""
summation_relation_yield_v1.py — the summation-polynomial / index-calculus object.

Closest thing to the actual ECDLP attack surface: a RELATION is a collinear triple
P1+P2+P3=O (i.e. S_3(x1,x2,x3)=0) with all three x-coords in a FACTOR BASE F. Index
calculus needs many relations; the RELATION YIELD (relations per factor-base element)
decides whether it beats brute force. The CM/GLV question: does a beta-INVARIANT factor
base (closed under x->beta x, beta^3=1) give higher yield than a random F of the same
size -- a factor-base COMPRESSION lever?

KNOWN part: j=0 curves have Aut(E)=mu_6, and automorphisms give a constant-factor index-
calculus speedup. OPEN part: anything BEYOND the trivial automorphism count.
So the sharp measurement is the ratio  yield(beta-invariant F) / yield(random F)  on the
CM curve, with a NON-CM control (y^2=x^3+x+1, Aut={+-1}, no beta) as the baseline.

PRIOR (stated up front): expect ~ the automorphism factor and nothing beyond. This
quantifies the exact lever on our curve family and checks for excess.

Exact: collinearity via the exact group law (integers). Averaged over many random F;
ratio is the reported statistic (float display only).
"""
import math, random
import numpy as np
from sympy import isprime
from hybrid_char_sum_v1 import legendre, tonelli


def curve_points(p, a, b):
    pts = []
    for x in range(p):
        r = (x * x * x + a * x + b) % p
        if r == 0:
            pts.append((x, 0))
        elif legendre(r, p) == 1:
            y = tonelli(r, p)
            pts.append((x, y)); pts.append((x, (p - y) % p))
    return pts


def padd(P, Q, p, a):
    if P is None: return Q
    if Q is None: return P
    (x1, y1), (x2, y2) = P, Q
    if x1 == x2 and (y1 + y2) % p == 0: return None
    if P == Q:
        if y1 == 0: return None
        lam = (3 * x1 * x1 + a) % p * pow(2 * y1, p - 2, p) % p
    else:
        lam = (y2 - y1) % p * pow((x2 - x1) % p, p - 2, p) % p
    x3 = (lam * lam - x1 - x2) % p
    return (x3, (lam * (x1 - x3) - y1) % p)


def cube_root(p):
    e = (p - 1) // 3; g = 2
    while pow(g, e, p) == 1: g += 1
    return pow(g, e, p)


def count_relations(pts_by_x, Fset, p, a):
    """# ordered collinear point-triples (P1,P2,P3=-(P1+P2)) with all x in Fset."""
    pts = [P for x in Fset for P in pts_by_x.get(x, [])]
    n = 0
    for i in range(len(pts)):
        for j in range(len(pts)):
            R = padd(pts[i], pts[j], p, a)
            if R is None:
                continue
            x3 = R[0]                    # P3 = -(Pi+Pj) has same x as R
            if x3 in Fset:
                n += 1
    return n


def x_orbits(xs, beta, p):
    """partition x-values into beta-orbits {x, beta x, beta^2 x}."""
    xs = set(xs); seen = set(); orbits = []
    b2 = (beta * beta) % p
    for x in xs:
        if x in seen: continue
        orb = {x, (beta * x) % p, (b2 * x) % p} & xs
        orbits.append(sorted(orb)); seen |= orb
    return orbits


def run(p, a, b, label, s_orbits, B, seed):
    pts = curve_points(p, a, b)
    by_x = {}
    for (x, y) in pts:
        by_x.setdefault(x, []).append((x, y))
    xs = list(by_x.keys())
    beta = cube_root(p)
    orbits = x_orbits(xs, beta, p)
    orbits3 = [o for o in orbits if len(o) == 3]        # full beta-orbits
    rng = random.Random(seed)

    # size: s x-values, a multiple of 3 so beta-invariant F is exact
    s = 3 * s_orbits
    yields_rand = []; yields_binv = []
    for _ in range(B):
        Frand = set(rng.sample(xs, s))
        yields_rand.append(count_relations(by_x, Frand, p, a) / (s ** 3 / p))
        if a == 0 and len(orbits3) >= s_orbits:          # beta-invariant only meaningful w/ CM
            chosen = rng.sample(orbits3, s_orbits)
            Fbinv = set(x for o in chosen for x in o)
            yields_binv.append(count_relations(by_x, Fbinv, p, a) / (s ** 3 / p))
    yr = float(np.mean(yields_rand))
    yb = float(np.mean(yields_binv)) if yields_binv else float('nan')
    ratio = yb / yr if yields_binv else float('nan')
    print(f"  {label:20} |E|={len(pts):>5} s={s:>3}  yield_rand={yr:6.3f}  "
          f"yield_betaInv={yb:6.3f}  ratio(binv/rand)={ratio:5.2f}")
    return yr, yb, ratio


def main():
    print("SUMMATION-POLYNOMIAL RELATION YIELD  (collinear triples in a factor base F)")
    print("=" * 80)
    print("Q: does a beta-invariant F beat a random F of the same size? (factor-base lever)")
    print("KNOWN: Aut(E)=mu_6 gives a constant-factor index-calculus speedup on j=0 curves.")
    print("Reported: ratio yield(beta-inv)/yield(random) on CM; non-CM = baseline.\n")
    for p in [1009, 4021, 10009]:
        if not isprime(p) or p % 3 != 1:
            continue
        s_orb = max(6, round(math.isqrt(p) / 3))          # s ~ sqrt p, multiple of 3
        print(f"p = {p}  (factor base ~ sqrt p):")
        run(p, 0, 7, "CM  y^2=x^3+7", s_orb, B=120, seed=p)
        run(p, 1, 1, "non-CM y^2=x^3+x+1", s_orb, B=120, seed=p + 1)
        print()
    print("READ: ratio ~ 1 => beta-invariance gives NO density advantage (automorphism just")
    print("      reshuffles).  ratio ~ 3 (=|beta-orbit|) => exactly the known Aut speedup.")
    print("      ratio growing with p, or >3 => a lever BEYOND the trivial automorphism count.")


if __name__ == "__main__":
    main()
