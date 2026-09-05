#!/usr/bin/env python3
"""
_dedekind_reduction_v1.py -- reduce BOTH open problems to a 1-parameter Dedekind region. Exact ints.

SETUP. eis: F_p -> rhombus P of L=(pi_p), reduced basis (R1,R2), coords (u,v) in [-1/2,1/2).
Babai rounds each coord independently => u(x)=cent(a x)/p, v(x)=cent(b x)/p for FIXED a,b in F_p^*,
cent(m) = representative of m mod p in (-p/2, p/2]. Substituting s=a x, r=b*a^{-1}:

   T+ = { x : u-v > 1/2 } = { s : cent(s) - cent(r s) > p/2 }        (s = a x, bijection)

PROBLEM 1 (H1 remaining lemma):   |T+_s| = 0 mod 6  <=>  chi2(2)=1.
PROBLEM 2 (S core):               S = (chi2(a)/3) * sum_{s in T+_s} chi2(s),
                                  and S=0 (when ORB even) <=> sum_{s in T+_s} chi2(s) = 0.

This script: (1) extracts a,b; (2) verifies u(x)=cent(ax)/p, v(x)=cent(bx)/p EXACTLY;
(3) computes r=b/a and identifies it (order, min poly -- is it omega? +-1? sqrt(-3)?);
(4) verifies T+ = {s: cent(s)-cent(rs)>p/2} exactly; (5) computes |T+| mod 6 and
sum_{T+} chi2(s), confirming Problems 1 & 2 in the s-picture. All exact.
"""
import sys
from fractions import Fraction as Fr
from sympy import isprime
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn

def cent(m, p):
    m %= p
    return m - p if 2 * m > p else m           # representative in (-p/2, p/2]

def analyze(p):
    chi2 = chi2_table(p)
    n = p + 1 + sum(chi2(((x * x % p) * x + 7) % p) for x in range(p))
    if not isprime(n): return None
    eis, eps, beta, R1, R2, DET = build(p)
    sig, orient = sigma_fn(p, eis, eps, R1, R2, DET)
    if sig is None: return {'p': p, 'FAIL': 'orient'}

    def coR(x):
        a, b = eis(x)
        u = Fr(a * R2[1] - b * R2[0], DET)
        v = Fr(b * R1[0] - a * R1[1], DET)
        return u, v

    # (1) extract a, b : p*u(x) = cent(a x). Use x=1..: a = cent-value * x^{-1}.
    def extract(coord_idx):
        vals = []
        for x in range(1, min(p, 50)):
            uv = coR(x)[coord_idx]
            m = uv * p                          # should be an integer = cent(a x)
            assert m.denominator == 1, f"p*coord not integer at p={p}"
            vals.append((x, int(m)))
        # a = m * x^{-1} for the first x with m != 0
        a = None
        for x, m in vals:
            if m % p != 0:
                a = m * pow(x, p - 2, p) % p
                break
        # verify consistency
        for x, m in vals:
            assert cent(a * x, p) == m, f"coord not cent(a x) at p={p}, x={x}: {cent(a*x,p)} vs {m}"
        return a
    a = extract(0); b = extract(1)

    # (2) full verification over ALL x
    ok = all(cent(a * x, p) == int(coR(x)[0] * p) and cent(b * x, p) == int(coR(x)[1] * p)
             for x in range(1, p))

    # (3) r = b/a, then rho = the order-6 unification: rho = r if orient '-' else -r.
    r = b * pow(a, p - 2, p) % p
    rho = r if orient == '-' else (p - r) % p       # fold orientation into sign
    rho_order = next(k for k in range(1, p) if pow(rho, k, p) == 1)
    is_prim6 = (rho * rho - rho + 1) % p == 0        # primitive 6th root: Phi_6(x)=x^2-x+1

    # (4) T+ in x-space vs unified s-space {s : cent(s) - cent(rho s) > p/2}
    Tx = set(x for x in range(1, p) if sig(x) == 1)
    Ts = set()
    ainv = pow(a, p - 2, p)
    for s in range(1, p):
        if cent(s, p) - cent(rho * s % p, p) > Fr(p, 2):
            Ts.add(s * ainv % p)                      # x = s / a
    match = (Tx == Ts)

    # (5) the two target quantities in the unified s-space
    Tp_s = [s for s in range(1, p) if cent(s, p) - cent(rho * s % p, p) > Fr(p, 2)]
    size = len(Tp_s)
    chi_sum = sum(chi2(s) for s in Tp_s)
    ORB = size // 3
    return {'p': p, 'a': a, 'b': b, 'r': r, 'rho': rho, 'rho_order': rho_order,
            'is_prim6': is_prim6, 'verify_ab': ok, 'Tpm_match': match, 'orient': orient,
            'Tp_size': size, 'Tp_mod6': size % 6, 'chi_sum': chi_sum, 'pmod8': p % 8,
            'chi2_2': chi2(2 % p), 'ORB': ORB}

def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
    print(f"# Unified Dedekind reduction, p in [{lo},{hi}), p=1 mod6, n prime")
    print(f"# rho = order-6 root (orient-folded).  T+_s = {{s: cent(s)-cent(rho s) > p/2}}")
    print(f"# {'p':>5} {'or':>3} {'rho':>6} {'ord':>4} {'prim6?':>6} {'ab':>4} "
          f"{'T+match':>8} {'|T+|%6':>6} {'chiSum':>7} {'m8':>3} {'x2(2)':>6}")
    allok = True; p1 = True; p2 = True
    for p in range(lo, hi):
        if p % 6 != 1 or not isprime(p) or p == 7: continue
        r = analyze(p)
        if r is None or 'FAIL' in r: continue
        allok &= r['verify_ab'] and r['Tpm_match']
        # Problem 1: |T+|%6 == 0 <=> chi2(2)=+1
        p1 &= ((r['Tp_mod6'] == 0) == (r['chi2_2'] == 1))
        # Problem 2: chi_sum == 0 <=> chi2(2)=+1  (S=0 exactly when ORB even)
        p2 &= ((r['chi_sum'] == 0) == (r['chi2_2'] == 1))
        print(f"  {r['p']:>5} {r['orient']:>3} {r['rho']:>6} {r['rho_order']:>4} "
              f"{str(r['is_prim6']):>6} {str(r['verify_ab'])[0]:>4} {str(r['Tpm_match']):>8} "
              f"{r['Tp_mod6']:>6} {r['chi_sum']:>7} {r['pmod8']:>3} {r['chi2_2']:>+6}")
    print(f"\n(reduction) u=cent(ax)/p, v=cent(bx)/p, T+ unified match: {allok}")
    print(f"(Problem 1)  |T+_s| = 0 mod 6  <=>  chi2(2)=+1 :  {p1}")
    print(f"(Problem 2)  sum_{{T+_s}} chi2(s) = 0  <=>  chi2(2)=+1 :  {p2}")

if __name__ == '__main__':
    main()
