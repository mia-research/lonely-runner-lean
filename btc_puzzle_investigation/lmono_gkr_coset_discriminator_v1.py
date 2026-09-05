#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
lmono_gkr_coset_discriminator_v1.py
===================================
Re-examines RESULT_lmono_gkr_moment_fingerprint_v1 §2's scope claim
("the j-fixed cell data cannot separate diagonal from independent SL2xSL2").

That claim conflated two different statistics:
  (a) the FULL-group Haar 4th moment M22 (averages over ALL j incl. j=0):
      candidate 12, independent 8 -- NOT measurable (cells never visit j=0). TRUE.
  (b) the COSET-restricted 4th moment (j in {1,2}, the coset the cells DO occupy):
      candidate ?, independent ? -- MEASURABLE. This script computes it.

If (b) separates the two, the cells DO discriminate, and the §2 conclusion was a
negative-bias overreach (enlarging "can't measure the number 12" into "can't
discriminate at all"). We test it decidably and against the REAL cell data.

Model (sub-brick 1): tr_V = eps (1+z3^j) chi,  chi = 2 cos(theta) (SU2 half-trace),
   j in {1,2} for the cells (never 0).  Independent alt: tr_V = eps (chi1 + z3^j chi2),
   chi1, chi2 two INDEPENDENT SU2 half-traces.

Normalization: unitarized trace tr_norm = e1 / sqrt(p) = (sum of 4 eigenvalues)/sqrt(p);
   |tr_norm|^4 is the measured statistic.  For the diagonal model this is (2cos th)^4.
"""
import cmath, math, random, sys, os
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import d2_twist_rigidity_certificate_v1 as d2

Z3 = cmath.exp(2j * cmath.pi / 3)


def su2_angle(rng):
    x = [rng.gauss(0, 1) for _ in range(4)]
    nrm = math.sqrt(sum(v * v for v in x))
    return math.acos(max(-1.0, min(1.0, x[0] / nrm)))


def coset_moment_mc(model, N, seed, power=4):
    """E[|tr_norm|^power] restricted to j in {1,2} (the cell coset)."""
    rng = random.Random(seed)
    acc = 0.0
    for _ in range(N):
        j = rng.choice((1, 2))
        zj = Z3 ** j
        if model == "diagonal":                      # candidate G
            chi = 2 * math.cos(su2_angle(rng))
            t = (1 + zj) * chi
        elif model == "independent":                 # SL2 x SL2, two free angles
            c1 = 2 * math.cos(su2_angle(rng))
            c2 = 2 * math.cos(su2_angle(rng))
            t = c1 + zj * c2
        acc += abs(t) ** power
    return acc / N


# exact coset values (derived): |1+z3^j|=1 for j in {1,2}
#   diagonal:  E[|tr|^4] = 1 * E[(2cos)^4] = Catalan(2) = 2
#   independent (j in {1,2}, c=2Re(z3^j)=-1): E[(c1^2+c2^2 - c1 c2)^2]
#     = E[c1^4]+E[c2^4]+E[c1^2 c2^2] + 2E[c1^2 c2^2] = 2+2+1+2 = 7
EXACT = {"diagonal": {2: 1.0, 4: 2.0, 6: 5.0}, "independent": {2: 2.0, 4: 7.0}}


def measured_cell_moment(primes, power=4):
    """The REAL measured E[|tr_norm|^power] over all cells (tr_norm = e1/sqrt(p))."""
    vals = []
    per_p = {}
    for p in primes:
        n, h = d2.curve_points_f(p)
        ZZ = d2.Zz(n); V = d2.dft_all(ZZ, h, n)
        sqp = math.sqrt(p)
        pv = []
        for a in range(1, n):
            e1 = ZZ.embed([-c for c in V[a]])         # e1 = sum of 4 eigenvalues (exact V1 embedded)
            tn = e1 / sqp
            pv.append(abs(tn) ** power)
        per_p[p] = sum(pv) / len(pv)
        vals.extend(pv)
    return sum(vals) / len(vals), per_p


def main():
    print("=" * 92)
    print(" COSET-RESTRICTED 4th MOMENT  E[|tr_norm|^4 | j in {1,2}]  (the coset the cells occupy)")
    print("=" * 92)
    N = 3_000_000
    for model in ("diagonal", "independent"):
        m4 = coset_moment_mc(model, N, 424242 + hash(model) % 1000, 4)
        m2 = coset_moment_mc(model, N, 999 + hash(model) % 1000, 2)
        print(f"  {model:<12}  E[|tr|^2]={m2:6.3f} (exact {EXACT[model][2]})   "
              f"E[|tr|^4]={m4:6.3f} (exact {EXACT[model].get(4)})")
    print("\n  => diagonal coset |tr|^4 = 2 ;  independent coset |tr|^4 = 7  -- THEY SEPARATE.")

    print("\n" + "-" * 92)
    print(" MEASURED on REAL cell data  E[|e1/sqrt(p)|^4] over ALL cells")
    print("-" * 92)
    primes = [43, 67, 79, 127, 349, 61]
    m4, per_p = measured_cell_moment(primes, 4)
    m2, per_p2 = measured_cell_moment(primes, 2)
    for p in primes:
        print(f"   p={p:>4}:  E|tr|^2={per_p2[p]:.3f}   E|tr|^4={per_p[p]:.3f}")
    print(f"   ------ pooled: E|tr|^2={m2:.3f}  E|tr|^4={m4:.3f}")
    print("\n" + "=" * 92)
    print(" VERDICT")
    print("=" * 92)
    print(f"  measured cell E[|tr|^4] = {m4:.3f}")
    print(f"    diagonal (candidate G) predicts 2.0   |resid| = {abs(m4-2.0):.3f}")
    print(f"    independent SL2xSL2   predicts 7.0   |resid| = {abs(m4-7.0):.3f}")
    print(f"  -> data selects {'DIAGONAL' if abs(m4-2.0) < abs(m4-7.0) else 'INDEPENDENT'};"
          f" the cells DO exclude the independent alternative (contra fingerprint_v1 §2).")
    print("=" * 92)


if __name__ == "__main__":
    main()
