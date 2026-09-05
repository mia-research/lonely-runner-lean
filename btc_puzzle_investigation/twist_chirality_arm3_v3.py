#!/usr/bin/env python3
"""
twist_chirality_arm3_v3.py -- ARM III, corrected slope (orientation-carrying coordinate).

DEVIATION FROM THE PRE-REGISTRATION (declared, with reason):
PREREG_twist_sum_B_closedform_v1.md section 7.1 identifies the `M` of the standing law
`sign(FLD) = -chi2(M)` with the CM quantity from `4p = L^2 + 27 M^2`.  That is a MISIDENTIFICATION.
The record's M (`RESULT_fld_classnumber_v2.md`, `_fld_L1_explore_v1.py:46`) is the **flap-coordinate
slope**: `t(X) := p*(u(X) - v(X))` is an integer in (-p,p) with `t(X) = M*X mod p`, M constant per
prime.  It is a function of the BASIS, not of the ideal.  The prereg's chirality parity derivation
(`M = v/3 -> -v/3`, ODD) therefore does not apply to the law under test.

Consequences for the arm, both handled here:
  (a) conjugation is the WRONG group element to test with -- and v1 showed why empirically
      (FLD' = FLD at 46/46).  There is a proof: X in Z is conjugation-fixed, and the lift takes
      coordinates w.r.t. the SAME basis that was conjugated, so eis'(X) = conj(eis(X)) has
      IDENTICAL coordinates (u,v).  Hence sigma' = sigma pointwise and every sigma-derived
      quantity is conjugation-INVARIANT.  Recorded here as an identity with its numerical check.
  (b) the live gauge group is the BASIS PRESENTATION group G (prereg 3.2), and v1 found
      sign(FLD) varies inside G at 46/46 primes.  So neither side of the standing law is a
      function of the ideal.  The question that remains -- and that this script answers -- is
      whether the law's two sides are gauge-COVARIANT TOGETHER:

          is   sign(FLD) * chi2(M_slope)   CONSTANT over the 8 presentations of the same lattice?

      YES  => the 54/54 is a relation between two orientation-odd objects, invariant under the
              gauge group, i.e. it says something about the lattice even though neither factor
              alone does.
      NO   => the 54/54 holds only in the basis that `cornacchia_4p_D3` + `gauss_reduce` happen
              to return; the law re-scopes to that convention, which is then named.

Exact integers / Fractions only.
"""
import sys
import time
from fractions import Fraction as Fr
from sympy import isprime

from lift_sextant_rhombus_law_proof_v2 import reduced_basis, enorm
from _sigma_chi2_scan_v1 import chi2_table
from twist_chirality_arm3_v1 import (build_from_basis, sigma_both, split_sums,
                                     conj, gauge_orbit, LM_from_lattice)


def slope_M(p, eis, R1, R2, DET, orient='-'):
    """the record's M: t(X) = p*(u(X)-v(X)) is an integer in (-p,p) with t(X) = M*X mod p.
    Returns (M, ok) where ok is False if the multiplier is not constant."""
    def co(w):
        a, b = w
        return Fr(a * R2[1] - b * R2[0], DET), Fr(b * R1[0] - a * R1[1], DET)
    M = None
    for X in range(1, p):
        u, v = co(eis(X))
        tt = ((u - v) if orient == '-' else (u + v)) * p
        if tt.denominator != 1:
            return None, False
        m = (int(tt) * pow(X, p - 2, p)) % p
        if M is None:
            M = m
        elif m != M:
            return None, False
    return M, True


def chi2v(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def evaluate_full(p, chi2, R1, R2):
    """FLD/A/B + slope M + sigma vector, for one basis presentation."""
    b = build_from_basis(p, R1, R2)
    if b is None:
        return {'FAIL': 'beta-ambiguous'}
    eis, eps, beta, _, _, DET = b
    sig, orient, npass, _ = sigma_both(p, eis, eps, R1, R2, DET)
    if sig is None:
        return {'FAIL': 'no-orientation'}
    r = split_sums(p, chi2, sig)
    M, ok = slope_M(p, eis, R1, R2, DET, orient)
    r.update({'M': M, 'M_const': ok, 'orient': orient, 'beta': beta, 'npass': npass,
              'sigvec': tuple(sig(x) for x in range(p))})
    return r


def run_prime(p, chi2):
    R1, R2 = reduced_basis(p)
    base = evaluate_full(p, chi2, R1, R2)
    if 'FAIL' in base:
        return {'p': p, 'FAIL': base['FAIL']}

    # (a) conjugation -- the PROVED-invariance check, now including sigma pointwise
    R1c, R2c = conj(R1), conj(R2)
    cj = evaluate_full(p, chi2, R1c, R2c)
    if 'FAIL' in cj:
        return {'p': p, 'FAIL': 'conj:' + cj['FAIL']}
    sig_identical = (cj['sigvec'] == base['sigvec'])

    # (b) the gauge orbit: is sign(FLD)*chi2(M) constant?
    prods, flds, Ms, oks = [], [], [], 0
    for (X, Y) in gauge_orbit(R1, R2):
        rg = evaluate_full(p, chi2, X, Y)
        if 'FAIL' in rg or not rg['M_const']:
            continue
        oks += 1
        flds.append(rg['FLD'])
        Ms.append(rg['M'])
        s = 1 if rg['FLD'] > 0 else (-1 if rg['FLD'] < 0 else 0)
        prods.append(s * chi2v(rg['M'], p))

    lm = LM_from_lattice(p, R1)
    return {
        'p': p, 'FLD': base['FLD'], 'B': base['B'], 'A': base['A'],
        'M': base['M'], 'M_const': base['M_const'], 'orient': base['orient'],
        'law_base': (1 if base['FLD'] > 0 else -1) == -chi2v(base['M'], p),
        'sig_identical_under_conj': sig_identical,
        'FLDc': cj['FLD'], 'Bc': cj['B'], 'Mc': cj['M'],
        'g_ok': oks, 'g_prod_set': sorted(set(prods)), 'g_fld_signs': sorted(set(
            1 if f > 0 else (-1 if f < 0 else 0) for f in flds)),
        'g_M_chi_set': sorted(set(chi2v(m, p) for m in Ms)),
        'CM_LM': lm,
    }


def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 2500
    t0 = time.time()
    rows, fails = [], []
    for p in range(lo, hi):
        if p % 24 != 19 or not isprime(p):
            continue
        r = run_prime(p, chi2_table(p))
        (rows if 'FAIL' not in r else fails).append(r)

    print(f"# ARM III v2 -- gauge behaviour of the sign law.  p = 19 mod 24, p in [{lo},{hi}).")
    print(f"# primes = {len(rows)}   excluded = {len(fails)}  {[f['p'] for f in fails]}")
    print()
    print(f"# {'p':>5} {'FLD':>5} {'B':>5} {'Mslope':>7} {'chi2M':>6} {'or':>3} {'law':>5} "
          f"{'|G|':>4} {'G:sign(FLD)':>12} {'G:chi2(M)':>11} {'G:PRODUCT':>11} {'conj sigma==':>13}")
    n_law = n_sig_id = 0
    prod_const = 0
    prod_values = {}
    for r in rows:
        n_law += r['law_base']
        n_sig_id += r['sig_identical_under_conj']
        pc = len(r['g_prod_set']) == 1
        prod_const += pc
        if pc:
            prod_values[r['g_prod_set'][0]] = prod_values.get(r['g_prod_set'][0], 0) + 1
        print(f"  {r['p']:>5} {r['FLD']:>5} {r['B']:>5} {str(r['M']):>7} "
              f"{chi2v(r['M'], r['p']):>6} {r['orient']:>3} {str(r['law_base']):>5} "
              f"{r['g_ok']:>4} {str(r['g_fld_signs']):>12} {str(r['g_M_chi_set']):>11} "
              f"{str(r['g_prod_set']):>11} {str(r['sig_identical_under_conj']):>13}")

    N = len(rows)
    print()
    print("## REGRESSION on the standing law (canonical basis)")
    print(f"  sign(FLD) = -chi2(M_slope)                     : {n_law}/{N}")
    print()
    print("## (a) CONJUGATION -- claimed identity: sigma is conjugation-invariant")
    print(f"  sigma' == sigma pointwise                      : {n_sig_id}/{N}")
    print(f"  FLD' == FLD                                    : "
          f"{sum(1 for r in rows if r['FLDc'] == r['FLD'])}/{N}")
    print(f"  M_slope' == M_slope                            : "
          f"{sum(1 for r in rows if r['Mc'] == r['M'])}/{N}")
    print()
    print("## (b) GAUGE ORBIT G (8 presentations of the SAME lattice)")
    print(f"  primes where sign(FLD) takes both signs in G   : "
          f"{sum(1 for r in rows if len(r['g_fld_signs']) > 1)}/{N}")
    print(f"  primes where chi2(M_slope) takes both signs    : "
          f"{sum(1 for r in rows if len(r['g_M_chi_set']) > 1)}/{N}")
    print(f"  ** primes where the PRODUCT is CONSTANT over G : {prod_const}/{N} **")
    print(f"     constant value -> count                     : {prod_values}")
    print(f"\n# elapsed {time.time()-t0:.1f}s")


if __name__ == '__main__':
    main()
