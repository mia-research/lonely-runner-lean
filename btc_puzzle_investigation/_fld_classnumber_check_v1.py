#!/usr/bin/env python3
"""
_fld_classnumber_check_v1.py -- is FLD(p) a CLASS NUMBER?  Exact ints only.

FROM THE HUNT: FLD = 2 sum_{T+} chi2 = 6 * (imbalance of QR/NQR mu3-orbits in the triangle T+).
Observed FLD/6 at p=19 mod24: 163->1, 211->-3, 547->-3, 907->3, 1051->-5 -- magnitudes
{1,3,3,3,5} = h(-163),h(-211),h(-547),h(-907),h(-1051).  CONJECTURE:

    FLD(p) = 0                     unless p = 19 mod 24
    |FLD(p)| = 6 * h(-p)           when p = 19 mod 24   (h = class number of Q(sqrt(-p)))

This ties the sigma*chi2 conservation to the class number -- an arithmetic object OUTSIDE the
curve's F_p symmetry.  Dirichlet: for p=3 mod4, sum_{a=1}^{(p-1)/2} chi2(a) = (2-chi2(2)) h(-p);
the chi2(2) factor is exactly the p mod 8 dependence the hunt isolated.
VERIFY: FLD vs 6*h(-p) with sign, across all p=1 mod6 (no n-prime filter -- FLD needs only sigma,chi2).
"""
import sys
from sympy import isprime
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn


def classnum_neg(p):
    """h(-p) for p = 3 mod 4 prime (fundamental disc D=-p): count reduced forms |b|<=a<=c."""
    D = -p; h = 0; a = 1
    while 3 * a * a <= p:
        for b in range(-a, a + 1):
            num = b * b - D
            if num % (4 * a):
                continue
            c = num // (4 * a)
            if c < a:
                continue
            if (abs(b) == a or a == c) and b < 0:
                continue
            h += 1
        a += 1
    return h


def fld(p):
    chi2 = chi2_table(p)
    eis, eps, beta, R1, R2, DET = build(p)
    sig, orient = sigma_fn(p, eis, eps, R1, R2, DET)
    if sig is None:
        return None
    return sum(sig(x) * chi2(x) for x in range(p))


def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    print("# FLD vs class number h(-p).  Conjecture: FLD=0 unless p=19 mod24; |FLD|=6 h(-p) there.")
    print(f"# {'p':>5} {'m24':>4} {'FLD':>6} {'FLD/6':>6} {'h(-p)':>6} {'|FLD/6|==h':>10} {'sign':>5}")
    ok_nonzero = ok_zero = 0
    bad = []
    for p in range(lo, hi):
        if p % 6 != 1 or not isprime(p) or p == 7:
            continue
        F = fld(p)
        if F is None:
            continue
        m24 = p % 24
        if m24 == 19:
            h = classnum_neg(p)
            match = (abs(F) == 6 * h) and (F % 6 == 0)
            sign = "+" if F > 0 else "-"
            ok_nonzero += 1 if match else 0
            if not match:
                bad.append(p)
            print(f"  {p:>5} {m24:>4} {F:>6} {F // 6:>6} {h:>6} {str(match):>10} {sign:>5}")
        else:
            if F == 0:
                ok_zero += 1
            else:
                bad.append(p)
                print(f"  {p:>5} {m24:>4} {F:>6}  <-- NONZERO off p=19 mod24 (violates conjecture)")
    print()
    print(f"|FLD/6| == h(-p) at p=19 mod24 : {ok_nonzero} matches" + (f"  BAD={bad}" if bad else "  (all)"))
    print(f"FLD == 0 off p=19 mod24        : {ok_zero} primes")
    if not bad:
        print("CONJECTURE HOLDS on this range.")


if __name__ == "__main__":
    main()
