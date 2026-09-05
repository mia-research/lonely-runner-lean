#!/usr/bin/env python3
"""
twist_gauge_covariance_v1.py -- the definitive run for ARM III of
PREREG_twist_sum_B_closedform_v1.md, with two declared corrections to the prereg (see below).

WHAT THIS MEASURES
  The standing law  sign(FLD) = -chi2(M)  (record: 54/54, RESULT_fld_classnumber_v2.md) was flagged
  there as possibly an artifact: "an internal consistency between two reduced-basis-dependent
  quantities, NOT a deeper arithmetic symmetry."  Both sides do depend on the basis.  The decidable
  question is whether they depend on it the SAME way, i.e. whether the PRODUCT
        Pi(p) := sign(FLD) * chi2(M)
  is invariant under the gauge group of basis presentations of the SAME ideal.

TWO CORRECTIONS TO THE PRE-REGISTRATION (declared, with reasons)
  C1. Prereg 7.1 identifies M with the CM quantity from 4p = L^2 + 27 M^2.  That is a
      misidentification: the record's M is the flap-coordinate SLOPE, t(X) = M*X mod p, where
      t(X) := p * s(X) and s is the ORIENTATION-CARRYING coordinate combination (u-v at
      orient '-', u+v at orient '+').  Reproduction check: the orientation-aware slope gives the
      law at 46/46 in-sample; the always-(u-v) reading gives 29/46 and the always-(u+v) 38/46.
      Since the CM M is conjugation-odd but the slope M is not a function of the ideal at all,
      the prereg's chirality derivation does not apply to the law under test.
  C2. Prereg 7.2/7.3's conjugation arm is degenerate, with a proof: every X in Z is fixed by
      conjugation and the lift takes coordinates w.r.t. the basis that was conjugated, so
      eis'(X) = conj(eis(X)) has IDENTICAL coordinates (u,v).  Hence sigma' = sigma POINTWISE and
      every sigma-derived quantity is conjugation-invariant.  Verified below, not assumed.
      The live gauge group is therefore the presentation group G of prereg 3.2, not conjugation.

  C3 (scope, found by this run).  `_twist_split_B_v1.run` computes FLD as A + B, which partitions
      F_p by chi2(x^3+7) = +1 / -1 and so DROPS the (up to 3) abscissae with x^3 = -7 -- the
      2-torsion x-coordinates, present exactly when -7 is a cube mod p.  The exact identity is
        FLD = A + B + corr,   corr := sum_{x^3 = -7} sigma(x) chi2(x)
      verified 206/206 below; corr != 0 at 16 of 206 primes.  The source scripts' `n` prime filter
      silently excluded these curves; the prereg deliberately DROPPED that filter (its section 6.1),
      which is what exposed the gap.  secp is unaffected: -7 is a non-cube mod secp's p [PROVED,
      on record], so E(F_p)[2] = 0 and corr = 0 identically there.  This script uses the TRUE FLD.

Exact integers / Fractions only.  No float.
"""
import sys
import time
from fractions import Fraction as Fr
from sympy import isprime

from lift_sextant_rhombus_law_proof_v2 import reduced_basis, enorm
from _sigma_chi2_scan_v1 import chi2_table
from twist_chirality_arm3_v1 import (build_from_basis, sigma_both, split_sums,
                                     conj, gauge_orbit)


def chi2v(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def sgn(v):
    return 0 if v == 0 else (1 if v > 0 else -1)


def evaluate(p, chi2, R1, R2):
    """One basis presentation -> sigma vector, slope M, and the exact sums."""
    b = build_from_basis(p, R1, R2)
    if b is None:
        return {'FAIL': 'beta-ambiguous'}
    eis, eps, beta, _, _, DET = b
    sig, orient, npass, _ = sigma_both(p, eis, eps, R1, R2, DET)
    if sig is None:
        return {'FAIL': 'no-orientation'}

    def co(w):
        a, b_ = w
        return Fr(a * R2[1] - b_ * R2[0], DET), Fr(b_ * R1[0] - a * R1[1], DET)

    M = None
    for X in range(1, p):
        u, v = co(eis(X))
        tt = ((u - v) if orient == '-' else (u + v)) * p
        if tt.denominator != 1:
            return {'FAIL': 'slope-nonintegral'}
        m = (int(tt) * pow(X, p - 2, p)) % p
        if M is None:
            M = m
        elif m != M:
            return {'FAIL': 'slope-nonconstant'}

    sg = [sig(x) for x in range(p)]
    r = split_sums(p, chi2, sig)
    tors = [x for x in range(p) if (x * x % p) * x % p == (-7) % p]
    r['corr'] = sum(sg[x] * chi2(x) for x in tors)
    r['FLD_true'] = sum(sg[x] * chi2(x) for x in range(p))
    r.update({'M': M, 'orient': orient, 'npass': npass, 'sig': sg, 'ntors': len(tors)})
    return r


def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 6000
    split = int(sys.argv[3]) if len(sys.argv) > 3 else 2500     # IS / OOS1 boundary
    t0 = time.time()

    id_ok = id_tot = 0            # C3 identity, over ALL p = 1 mod 6
    corr_nz = []
    stats = {}                    # window -> counters

    for p in range(lo, hi):
        if p % 6 != 1 or not isprime(p):
            continue
        rb = reduced_basis(p)
        if rb is None:
            continue
        R1, R2 = rb
        chi2 = chi2_table(p)
        base = evaluate(p, chi2, R1, R2)
        if 'FAIL' in base:
            continue

        # ---- C3: the exact identity, all p = 1 mod 6
        id_tot += 1
        id_ok += (base['FLD_true'] == base['A'] + base['B'] + base['corr'])
        if base['corr'] != 0:
            corr_nz.append(p)

        if p % 24 != 19:
            continue                       # SCOPE: the law lives at p = 19 mod 24
        w = 'IS' if p < split else 'OOS1'
        s = stats.setdefault(w, {'N': 0, 'law': 0, 'gN': 0, 'geq': 0, 'eps': {},
                                 'pconst': 0, 'pvals': {}, 'fldsign_varies': 0,
                                 'chiM_varies': 0, 'absfld': 0, 'conj': 0})
        s['N'] += 1
        s['law'] += (sgn(base['FLD_true']) == -chi2v(base['M'], p))

        # ---- C2: conjugation acts trivially (claimed identity, checked)
        cj = evaluate(p, chi2, conj(R1), conj(R2))
        if 'FAIL' not in cj:
            s['conj'] += (cj['sig'] == base['sig'] and cj['FLD_true'] == base['FLD_true']
                          and cj['M'] == base['M'])

        # ---- the gauge orbit
        prods, fsigns, chims = set(), set(), set()
        for (X, Y) in gauge_orbit(R1, R2):
            g = evaluate(p, chi2, X, Y)
            if 'FAIL' in g:
                continue
            s['gN'] += 1
            s['absfld'] += (abs(g['FLD_true']) == abs(base['FLD_true']))
            # gauge equivariance: sigma_g(x) = eps * sigma(c x),  c = M_g / M
            c = (g['M'] * pow(base['M'], p - 2, p)) % p
            e = None
            for ee in (1, -1):
                if all(g['sig'][x] == ee * base['sig'][(c * x) % p] for x in range(p)):
                    e = ee
                    break
            s['geq'] += (e is not None)
            s['eps'][e] = s['eps'].get(e, 0) + 1
            cm = chi2v(g['M'], p)
            fsigns.add(sgn(g['FLD_true']))
            chims.add(cm)
            prods.add(sgn(g['FLD_true']) * cm)
        s['fldsign_varies'] += (len(fsigns) > 1)
        s['chiM_varies'] += (len(chims) > 1)
        s['pconst'] += (len(prods) == 1)
        for v in prods:
            s['pvals'][v] = s['pvals'].get(v, 0) + 1

    print(f"# twist_gauge_covariance_v1 -- p in [{lo},{hi}), IS/OOS1 split at {split}")
    print()
    print("## C3 -- the exact decomposition identity (all p = 1 mod 6)")
    print(f"   FLD = A + B + corr, corr over the 2-torsion abscissae : {id_ok}/{id_tot}")
    print(f"   primes with corr != 0 (A+B alone is WRONG there)      : {len(corr_nz)}/{id_tot}")
    print(f"   {corr_nz}")
    print()
    for w in ('IS', 'OOS1'):
        if w not in stats:
            continue
        s = stats[w]
        print(f"## {w}  (p = 19 mod 24)   primes N = {s['N']}, gauge instances = {s['gN']}")
        print(f"   standing law  sign(FLD) = -chi2(M_slope)          : {s['law']}/{s['N']}")
        print(f"   C2  conjugation acts trivially (sigma,FLD,M)      : {s['conj']}/{s['N']}")
        print(f"   |FLD| constant over the gauge orbit               : {s['absfld']}/{s['gN']}")
        print(f"   sign(FLD) takes BOTH signs within the orbit       : {s['fldsign_varies']}/{s['N']}")
        print(f"   chi2(M)   takes BOTH signs within the orbit       : {s['chiM_varies']}/{s['N']}")
        print(f"   gauge equivariance sigma_g = eps*sigma(c.)        : {s['geq']}/{s['gN']}"
              f"   eps distribution: {s['eps']}")
        print(f"** PRODUCT sign(FLD)*chi2(M) constant over the orbit : {s['pconst']}/{s['N']}"
              f"   values: {s['pvals']} **")
        print()
    print(f"# elapsed {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
