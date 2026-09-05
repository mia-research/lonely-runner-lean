#!/usr/bin/env python3
"""
easy_target_predict_v1.py — LINE 1: is "easy-target-ness" a property of R (exploitable)
or of the (R,F) pairing (not)?

v10: decomposition count c(R) over targets is over-dispersed (some R decompose many more
ways). A LEVER would be: a CHEAP readout of R predicts high c(R) => target selection. But
first the disjoint-attribution question (residue-vs-component discipline):
  * INTRINSIC (property of R): c-bar(R)=mean_F c(R,F) varies across R beyond sampling noise
    => some R are intrinsically easy => a readout of R could predict it => LEVER.
  * F-SPECIFIC (property of the pairing): c-bar(R) FLAT (variation = sampling noise) => the
    easy targets are an artifact of the chosen F => NO readout of R can predict it.
Translation-covariance predicts FLAT (F+Q is an equidistributed base for every Q, so
E_F[c(R)] is the same for all R). We MEASURE it rather than assume.

Test A: fixed targets x many random F -> is Var_R(c-bar) = sampling noise (ratio ~1)?
Test B: the one escape hatch -- a STRUCTURED (beta-invariant) F breaks translation-
        covariance; does R's geometry (mu_3-orbit size, eps, sextant, norm) then predict
        c(R,F)?  MI + shuffle null + the disjoint-attribution check.

Exact group law; MI/variance are ranked/display floats.
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


def padd(P, Q, p, a=0):
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


def decomp_counts(F, targets, p):
    pair = defaultdict(int)
    for P1 in F:
        for P2 in F:
            pair[padd(P1, P2, p)] += 1
    out = []
    for R in targets:
        c = 0
        for P3 in F:
            need = padd(R, (P3[0], (-P3[1]) % p), p)
            c += pair.get(need, 0)
        out.append(c)
    return np.array(out, float)


def mi_bits(a, b, nbins=8):
    a = np.asarray(a); b = np.asarray(b)
    ab = np.digitize(a, np.quantile(a, np.linspace(0, 1, nbins + 1)[1:-1]))
    bb = np.digitize(b, np.quantile(b, np.linspace(0, 1, nbins + 1)[1:-1]))
    N = len(a); mi = 0.0
    for i in set(ab):
        for j in set(bb):
            nij = np.sum((ab == i) & (bb == j))
            if nij == 0: continue
            pij = nij / N; pi = np.mean(ab == i); pj = np.mean(bb == j)
            mi += pij * math.log2(pij / (pi * pj))
    return mi


def main():
    print("LINE 1: easy-target-ness -- property of R (LEVER) or of the (R,F) pairing (not)?")
    print("=" * 82)
    for p in [2011, 10009]:
        if not isprime(p) or p % 3 != 1:
            continue
        pts = curve_points(p, 0, 7)
        by_x = defaultdict(list)
        for P in pts: by_x[P[0]].append(P)
        xs = list(by_x.keys())
        beta = cube_root(p); b2 = beta * beta % p
        eis, eps = build(p)
        rng = random.Random(p)
        s = 3 * max(6, round(math.isqrt(p) / 3))
        M = 150
        targets = [pts[rng.randrange(len(pts))] for _ in range(M)]

        # Test A: many random F -> is c-bar(R) flat?
        B = 60
        C = np.zeros((M, B))
        for j in range(B):
            Fx = rng.sample(xs, s)
            F = [P for x in Fx for P in by_x[x]]
            C[:, j] = decomp_counts(F, targets, p)
        cbar = C.mean(axis=1)                      # per-target mean over F
        var_across_targets = cbar.var()
        sampling_var = (C.var(axis=1) / B).mean()  # expected var of cbar if targets identical
        ratio = var_across_targets / (sampling_var + 1e-12)
        print(f"p={p}: Test A  Var_R(c-bar)/sampling-noise = {ratio:.2f}  "
              f"(~1 => FLAT: easy-targetness is F-specific, NOT intrinsic to R; >>1 => intrinsic)")

        # Test B: structured (beta-invariant) F -- does R geometry predict c(R,F)?
        seen = set(); orbs = []
        for x in xs:
            if x in seen: continue
            o = {x, beta * x % p, b2 * x % p} & set(xs); orbs.append(sorted(o)); seen |= o
        orbs3 = [o for o in orbs if len(o) == 3]
        Fbx = [x for o in rng.sample(orbs3, s // 3) for x in o]
        Fb = [P for x in Fbx for P in by_x[x]]
        cB = decomp_counts(Fb, targets, p)
        # readouts of R (cheap): eps, norm s, sextant proxy (u sign), mu3-orbit "closedness"
        def lift(x): return eis(x)
        norm_R = np.array([(lambda uv: uv[0]**2 - uv[0]*uv[1] + uv[1]**2)(lift(R[0])) / p for R in targets])
        eps_R = np.array([0 if eps(R[0]) == 0 else 1 for R in targets])
        # is R's x in a full beta-orbit inside Fbx-closure? (structured-F alignment readout)
        Fset = set(Fbx)
        align_R = np.array([1 if (beta * R[0] % p in Fset or R[0] in Fset) else 0 for R in targets])
        print(f"        Test B (beta-inv F): MI(c ; norm_R)={mi_bits(cB, norm_R):.4f}  "
              f"MI(c ; eps_R)={mi_bits(cB, eps_R):.4f}  MI(c ; align_R)={mi_bits(cB, align_R):.4f}  bits")
        # shuffle null for the strongest readout
        best = max(mi_bits(cB, norm_R), mi_bits(cB, align_R))
        nulls = [mi_bits(cB, norm_R[rng.sample(range(M), M)]) for _ in range(200)]
        pval = (sum(1 for t in nulls if t >= best) + 1) / (len(nulls) + 1)
        print(f"        strongest readout MI={best:.4f}, shuffle-null p={pval:.3f}  "
              f"(self-MI c;c = {mi_bits(cB, cB):.3f} fires)")
        print()
    print("READ: Test A ~1 => easy-targetness is a pairing artifact (no R-readout lever, matches")
    print("      translation-covariance).  Test B MI small & p>0.05 => even a structured base")
    print("      leaves R's geometry unpredictive of decomposition => no target-selection lever.")


if __name__ == "__main__":
    main()
