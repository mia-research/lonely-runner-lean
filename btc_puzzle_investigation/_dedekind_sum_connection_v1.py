#!/usr/bin/env python3
"""
_dedekind_sum_connection_v1.py -- pin the EXACT classical object behind P1 and P2. Exact rationals.

Both problems live on  T+ = {s in F_p*: cent(s) - cent(rho s) > p/2},  rho^2 - rho + 1 = 0
(primitive 6th root). This script identifies the classical invariant that controls them:

  * N = |T+| = 3*ORB.  Classical lattice-count identities relate #{s: cent(s)-cent(rho s)>p/2}
    to the DEDEKIND SUM s(rho, p) = sum_{i=1}^{p-1} ((i/p))((rho i/p)).
  * P1 wants N mod 6 (i.e. ORB mod 2) = (chi2(2)==-1).
  * P2 wants the chi2-weighted sum S' = sum_{s in T+} chi2(s) to vanish iff chi2(2)=1.

Checks, all exact:
  (A) Dedekind sum s(rho,p) as an exact Fraction; its denominator / 2-adic valuation vs chi2(2).
  (B) N vs a closed form in s(rho,p): the standard  #{cent(s)-cent(rs)>p/2}  count.
  (C) For P2: is S' a JACOBI-sum-type object? test S' vs chi2/chi3 Jacobi sums and class number h(-p).
  (D) direct: tabulate (chi2(2), N mod 6, S', 12*s(rho,p)) to expose the exact link.
"""
import sys
from fractions import Fraction as Fr
from sympy import isprime, jacobi_symbol
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn

def cent(m, p):
    m %= p
    return m - p if 2 * m > p else m

def saw(a, k):                      # ((a/k)) Dedekind sawtooth, exact Fraction
    a %= k
    if a == 0: return Fr(0)
    return Fr(a, k) - Fr(1, 2)

def dedekind(h, k):                 # s(h,k) exact
    return sum(saw(i, k) * saw(h * i, k) for i in range(1, k))

def rho_of(p):
    """primitive 6th root of unity mod p: root of x^2-x+1."""
    # (1 + sqrt(-3))/2 ; need sqrt(-3) mod p (exists, p=1 mod 3)
    from sympy.ntheory.residue_ntheory import sqrt_mod
    r3 = sqrt_mod((-3) % p, p)
    inv2 = pow(2, p - 2, p)
    for cand in ((1 + r3) * inv2 % p, (1 - r3) * inv2 % p):
        if (cand * cand - cand + 1) % p == 0:
            return cand
    return None

def analyze(p):
    chi2 = chi2_table(p)
    n = p + 1 + sum(chi2(((x * x % p) * x + 7) % p) for x in range(p))
    if not isprime(n): return None
    rho = rho_of(p)
    Tp = [s for s in range(1, p) if cent(s, p) - cent(rho * s % p, p) > Fr(p, 2)]
    N = len(Tp)
    Sprime = sum(chi2(s) for s in Tp)
    ds = dedekind(rho, p)                          # Dedekind sum, exact Fraction
    return {'p': p, 'rho': rho, 'N': N, 'ORB': N // 3, 'Nmod6': N % 6, 'Sprime': Sprime,
            'ded': ds, '12ded': 12 * ds, 'chi2_2': chi2(2 % p), 'pmod8': p % 8}

def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 900
    print(f"# Dedekind-sum connection, p in [{lo},{hi}), p=1 mod6, n prime")
    print(f"# {'p':>5} {'m8':>3} {'x2(2)':>5} {'N':>5} {'ORB':>4} {'N%6':>4} {'Sprime':>7} "
          f"{'s(rho,p)':>12} {'12s':>8} {'12s%?':>6}")
    for p in range(lo, hi):
        if p % 6 != 1 or not isprime(p) or p == 7: continue
        r = analyze(p)
        if r is None: continue
        d = r['ded']
        s12 = r['12ded']
        print(f"  {r['p']:>5} {r['pmod8']:>3} {r['chi2_2']:>+5} {r['N']:>5} {r['ORB']:>4} "
              f"{r['Nmod6']:>4} {r['Sprime']:>7} {str(d):>12} {str(s12):>8} "
              f"{str(s12.numerator % 4 if s12.denominator==1 else 'nonint'):>6}")
    print("\nLooking for: an exact function of s(rho,p) whose parity / 2-adic val = chi2(2).")
    print("If 12*s(rho,p) is an integer with a clean mod-4 (or mod-8) tie to chi2(2), that closes P1.")

if __name__ == '__main__':
    main()
