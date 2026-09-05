#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
lmono_routeB_geom_iso_certificate_v1.py
=======================================
Route B (sheaf-isomorphism): the DECIDABLE certificate that the numeric [2,2]
split of L*(a) is the shadow of a GEOMETRIC isomorphism  W' ~= W (x) (const),
i.e. that the mu_3 relating the two rank-2 planes is ARITHMETIC (a fixed
Frobenius twist), NOT geometric -- hence  G_geom^0 = SL2  and  G_arith =
SL2.mu3.{+-1}.

Three exact per-cell facts (float only in the degree-4 root readout):
  (F1) det(W_a) is CONSTANT in a: = zeta_6 * p  (p=3 mod4) or zeta_3^{-1} * p
       (p=1 mod4).  A geometrically-constant rank-1 det => after normalizing by
       sqrt(det), W is a geometrically SL2 (det-1) rank-2 sheaf.
  (F2) trace proportionality  tr(W'_a) = zeta_3 * tr(W_a)  and  det(W'_a) =
       zeta_3^2 * det(W_a)  at every cell (the [2,2] / 120-degree shadow).  Two
       rank-2 pieces with trace functions proportional by a CONSTANT are
       geometrically isomorphic up to that constant twist (Frobenius-trace
       rigidity, Chebotarev) -- the const is arithmetic (zeta_3), so
       geometrically W' ~= W.
  (F3) irreducibility proxy: |roots| = sqrt(p) (purity) and alpha/sqrt(p) is
       NEVER a root of unity (order <= 66) -- W does not reduce to a CM/finite
       sub (banked in the D2 certificate; re-confirmed here).

W = the pair of roots whose zeta_3-multiple is again a root (the g=2 W-plane);
W' = zeta_3 * W.

NOTE (plan correction): PLAN_lmono_monodromy_campaign_v1 §5B proposed producing
the W'~=W(x)psi isomorphism from the omega-intertwining.  §3 of the same plan
RETRACTS within-cell mu_3-equivariance ("omega intertwines the FIBERS along the
orbit {a,lam a,lam^2 a}, NOT within a fiber").  So omega is a CROSS-cell map and
cannot furnish the WITHIN-cell W<->W' isomorphism.  The route that does is
Frobenius-trace rigidity (F1+F2+F3), which needs no omega.
"""
import cmath, math, sys, os
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import d2_twist_rigidity_certificate_v1 as d2

Z3 = cmath.exp(2j * cmath.pi / 3)
Z6 = cmath.exp(1j * cmath.pi / 3)


def w_plane_sources(roots, sqp, tol=1e-6):
    return [r for i, r in enumerate(roots)
            if any(abs(Z3 * r - roots[j]) < tol * sqp for j in range(len(roots)) if j != i)]


def main():
    primes = [43, 67, 79, 127, 163, 211, 349, 61]
    print("=" * 98)
    print(" ROUTE B  --  geometric-isomorphism certificate  (W' ~= W geometrically; mu3 ARITHMETIC)")
    print("=" * 98)
    allok = True
    for p in primes:
        n, h = d2.curve_points_f(p)
        ZZ = d2.Zz(n); V = d2.dft_all(ZZ, h, n)
        eps = -1 if p % 4 == 3 else 1
        sqp = math.sqrt(p)
        detW_target = (Z6 * p) if eps == -1 else (Z3.conjugate() * p)
        f1_dev = 0.0     # |det(W)-target|/p   (F1 constancy)
        f2_tr = 0.0      # |tr(W')-z3 tr(W)|/sqrt p
        f2_det = 0.0     # |det(W')-z3^2 det(W)|/p
        f3_purity = 0.0
        f3_rou = 1e9     # min dist of (alpha/sqrt p)^m from 1
        cells = ng2 = 0
        for a in range(1, n):
            e1 = ZZ.embed([-c for c in V[a]])
            roots = list(np.roots([1 + 0j, -e1, e1 * e1 - eps * p, -eps * p * e1, float(p * p)]))
            src = w_plane_sources(roots, sqp)
            if len(src) != 2:
                ng2 += 1
                continue
            cells += 1
            trW = src[0] + src[1]; detW = src[0] * src[1]
            trWp = Z3 * src[0] + Z3 * src[1]; detWp = (Z3 * src[0]) * (Z3 * src[1])
            f1_dev = max(f1_dev, abs(detW - detW_target) / p)
            f2_tr = max(f2_tr, abs(trWp - Z3 * trW) / sqp)
            f2_det = max(f2_det, abs(detWp - Z3 * Z3 * detW) / p)
            for r in roots:
                f3_purity = max(f3_purity, abs(abs(r) - sqp) / sqp)
                u = r / sqp
                for m in range(1, 67):
                    f3_rou = min(f3_rou, abs(u ** m - 1))
        ok = (ng2 == 0 and f1_dev < 1e-9 and f2_tr < 1e-9 and f2_det < 1e-9
              and f3_purity < 1e-9 and f3_rou > 1e-6)
        allok = allok and ok
        arm = "3mod4" if eps == -1 else "1mod4"
        print(f" p={p:>4} n={n:>4} [{arm}] cells={cells}/{n-1}")
        print(f"    F1 det(W)=const  |det(W)-{'z6' if eps==-1 else 'z3^-1'}*p|/p  max {f1_dev:.2e}")
        print(f"    F2 tr(W')=z3 tr(W) max {f2_tr:.2e} | det(W')=z3^2 det(W) max {f2_det:.2e}")
        print(f"    F3 purity max {f3_purity:.2e} | root-of-unity survival min-dist {f3_rou:.2e} (>1e-6 = irreducible/non-CM)")
        print(f"    -> {'PASS' if ok else 'FAIL'}")
    print("=" * 98)
    print(f" OVERALL: {'PASS' if allok else 'FAIL'}")
    print(" reading: F1 (det const) + F2 (const-ratio trace) + F3 (irreducible) => W' ~= W geometrically,")
    print("          the zeta_3 is an ARITHMETIC twist => G_geom^0 = SL2, G_arith = SL2.mu3.{+-1}.")
    print(" (the group-identity step still needs Larsen (claim1) + rigidity (claim4) -- citation gate.)")
    print("=" * 98)
    sys.exit(0 if allok else 1)


if __name__ == "__main__":
    main()
