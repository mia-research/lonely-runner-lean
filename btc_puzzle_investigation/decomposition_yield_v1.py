#!/usr/bin/env python3
"""
decomposition_yield_v1.py — the index-calculus DECOMPOSITION step (Semaev S_4 rung).

v9 counted 3-term RELATIONS P1+P2+P3=O inside a factor base. The actual index-calculus
bottleneck is the DECOMPOSITION step: given a random target R in <G>, write R = P1+P2+P3
with all Pi in the factor base F (governed by the 4th summation polynomial S_4). The
relation YIELD = decompositions per target decides feasibility, and its cost/structure is
where the ASYMPTOTIC complexity of ECDLP lives -- NOT bounded by |Aut(E)|=6 the way a pure
symmetry lever is. So this is the honest place to look for structure that could SCALE.

Questions (each with a matched null + a scaling read in p):
  (1) yield(beta-invariant F) / yield(random F)  -- same as v9 but for DECOMPOSITION.
      If this exceeds the bounded automorphism factor OR grows with p => a real lever.
  (2) TARGET-DEPENDENCE: does R's own geometric label (core vs flap, eps) change how many
      ways it decomposes?  A target-dependent decomposition bias is NOT |Aut|-bounded and
      would be exploitable (some points cheap to decompose). Heuristic null: independent.
  (3) VARIANCE of the per-target yield vs the Poisson/heuristic prediction. Sub-Poisson
      (rigid) or a heavy tail (some targets very easy) = structure; Poisson = generic.

heuristic yield ~ |F|^3 / (6 * n) per target (unordered triples hitting a ~uniform R).
Exact group law (integers); ratios/variance are float display. Full enumeration small p.
"""
import math, random
from collections import defaultdict
import numpy as np
from sympy import isprime
from hybrid_char_sum_v1 import legendre, tonelli
from int1_frame_operator_v1 import build


def curve_points(p, a, b):
    pts = []
    for x in range(p):
        r = (x * x * x + a * x + b) % p
        if r == 0:
            pts.append((x, 0))
        elif legendre(r, p) == 1:
            y = tonelli(r, p); pts.append((x, y)); pts.append((x, (p - y) % p))
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


def decompose_counts(F, targets, p, a):
    """for each target R, # ordered (P1,P2,P3) in F^3 with P1+P2+P3 = R (as a point)."""
    # precompute all pairwise sums P1+P2 once
    pair = defaultdict(int)
    for P1 in F:
        for P2 in F:
            S = padd(P1, P2, p, a)
            pair[S] += 1                      # S may be None (identity)
    # R = S + P3  => S = R - P3 = R + (-P3)
    counts = {}
    for R in targets:
        c = 0
        for P3 in F:
            negP3 = (P3[0], (-P3[1]) % p)
            need = padd(R, negP3, p, a)        # S = R - P3
            c += pair.get(need, 0)
        counts[R] = c
    return counts


def run(p, a, b, s, B_targets, seed, do_beta):
    pts = curve_points(p, a, b)
    xs = list({P[0] for P in pts})
    by_x = defaultdict(list)
    for P in pts:
        by_x[P[0]].append(P)
    rng = random.Random(seed)
    beta = cube_root(p)

    # random factor base of s x-values (all points on them)
    Frx = rng.sample(xs, s)
    Fr = [P for x in Frx for P in by_x[x]]
    # targets: random points in the group
    targets = [pts[rng.randrange(len(pts))] for _ in range(B_targets)]
    cr = decompose_counts(Fr, targets, p, a)
    heur = (len(Fr) ** 3) / (len(pts))          # ordered triples / group size
    yr = np.mean(list(cr.values())) / heur

    # target-dependence: yield vs target's eps-label (CM only, needs lift)
    tdep = None
    if a == 0:
        eis, eps = build(p)
        by_lab = defaultdict(list)
        for R, c in cr.items():
            by_lab[0 if eps(R[0]) == 0 else 1].append(c)
        if by_lab[0] and by_lab[1]:
            tdep = (np.mean(by_lab[0]) / heur, np.mean(by_lab[1]) / heur)

    # variance ratio (Poisson => 1)
    vals = np.array(list(cr.values()), float)
    vr = float(vals.var() / (vals.mean() + 1e-12))

    yb = ratio = float('nan')
    if do_beta and a == 0:
        b2 = (beta * beta) % p
        orbs = []
        seen = set()
        for x in xs:
            if x in seen: continue
            o = {x, beta * x % p, b2 * x % p} & set(xs)
            orbs.append(sorted(o)); seen |= o
        orbs3 = [o for o in orbs if len(o) == 3]
        if len(orbs3) >= s // 3:
            chosen = rng.sample(orbs3, s // 3)
            Fbx = [x for o in chosen for x in o]
            Fb = [P for x in Fbx for P in by_x[x]]
            cb = decompose_counts(Fb, targets, p, a)
            heurb = (len(Fb) ** 3) / len(pts)
            yb = np.mean(list(cb.values())) / heurb
            ratio = yb / yr
    return yr, vr, tdep, ratio, len(pts)


def main():
    print("DECOMPOSITION YIELD  (index-calculus relation step: R = P1+P2+P3, Pi in F)")
    print("=" * 82)
    print("Not |Aut|-bounded like a pure symmetry lever -- the place asymptotic ECDLP cost")
    print("lives.  Testing: beta-inv/random ratio, TARGET-dependence (eps), variance vs Poisson.\n")
    print(f"{'p':>6} {'|E|':>6} {'s':>4} {'yield/heur':>10} {'var/Poisson':>11} "
          f"{'yield core|flap':>18} {'beta/rand':>9}")
    for p in [1009, 4021, 10009]:
        if not isprime(p) or p % 3 != 1:
            continue
        s = 3 * max(4, round(math.isqrt(p) / 4))
        yr, vr, tdep, ratio, ne = run(p, 0, 7, s, B_targets=300, seed=p, do_beta=True)
        td = f"{tdep[0]:.3f}|{tdep[1]:.3f}" if tdep else "   n/a"
        print(f"{p:>6} {ne:>6} {s:>4} {yr:>10.3f} {vr:>11.3f} {td:>18} {ratio:>9.2f}  CM")
        yr2, vr2, _, _, ne2 = run(p, 1, 1, s, B_targets=300, seed=p + 1, do_beta=False)
        print(f"{p:>6} {ne2:>6} {s:>4} {yr2:>10.3f} {vr2:>11.3f} {'   --':>18} {'  --':>9}  non-CM")
        print()
    print("READ: yield/heur ~ 1 = generic decomposition density.  var/Poisson ~ 1 = no easy-")
    print("      target tail.  core|flap equal = target label doesn't help.  beta/rand: >1 &")
    print("      GROWING with p, or var/Poisson growing = structure BEYOND the |Aut| ceiling.")


if __name__ == "__main__":
    main()
