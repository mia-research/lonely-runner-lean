#!/usr/bin/env python3
"""
_fld_interval_v1.py -- pin Sum_{T+} chi2 against classical interval/sextant character sums.
Exact ints. p = 3 mod 4 only (where FLD = 2 Sum_{T+} chi2).

SHARPENED TARGET:  Sum_{T+} chi2  =  +- D   at p=19 mod24,   = 0 at p=7 mod24,
where D = Sum_{a=1}^{(p-1)/2} chi2(a) = (2 - chi2(2)) h(-p) (Dirichlet, verified).

TEST decompositions that could explain the p mod 8 add/cancel:
  sextants  A6=(0,p/6] B6=(p/6,p/3] C6=(p/3,p/2]   (D = A6+B6+C6)
  quarters  E4=(0,p/4] F4=(p/4,p/2]                  (the chi2(2) fold lives here)
  thirds    T3=(0,p/3] and (p/3,p/2]
Report Sum_{T+}chi2 next to these, split by p mod 24, to read off the identity.
"""
import sys
from sympy import isprime
from _sigma_chi2_scan_v1 import chi2_table, build, sigma_fn


def classnum_neg(p):
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


def isum(chi2, lo, hi):
    return sum(chi2(a) for a in range(lo, hi + 1))


def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 900
    print("# Sum_{T+}chi2 vs interval/sextant sums. p=3 mod4. Tp=FLD/2. D=A6+B6+C6.")
    print(f"# {'p':>4} {'m24':>3} {'c2(2)':>5} {'h':>3} {'Tp':>4} {'D':>4} {'A6':>4} {'B6':>4} "
          f"{'C6':>4} {'E4':>4} {'F4':>4} {'Tp==?':>16}")
    for p in range(lo, hi):
        if p % 6 != 1 or not isprime(p) or p == 7 or p % 4 != 3:
            continue
        chi2 = chi2_table(p)
        eis, eps, beta, R1, R2, DET = build(p)
        sig, orient = sigma_fn(p, eis, eps, R1, R2, DET)
        if sig is None:
            continue
        FLD = sum(sig(x) * chi2(x) for x in range(p))
        Tp = FLD // 2
        h = classnum_neg(p)
        half = (p - 1) // 2
        A6 = isum(chi2, 1, p // 6)
        B6 = isum(chi2, p // 6 + 1, p // 3)
        C6 = isum(chi2, p // 3 + 1, half)
        E4 = isum(chi2, 1, p // 4)
        F4 = isum(chi2, p // 4 + 1, half)
        D = A6 + B6 + C6
        # try to name Tp among simple combinations
        cands = {
            'D': D, '-D': -D, 'A6': A6, 'B6': B6, 'C6': C6, '2A6': 2 * A6,
            '2C6': 2 * C6, 'A6-C6': A6 - C6, 'C6-A6': C6 - A6, 'E4-F4': E4 - F4,
            'F4-E4': F4 - E4, '2(A6+B6)-D': 2 * (A6 + B6) - D, 'D-2B6': D - 2 * B6,
            '2C6-D': 2 * C6 - D, 'A6+C6-B6': A6 + C6 - B6,
        }
        names = [k for k, v in cands.items() if v == Tp]
        print(f"  {p:>4} {p%24:>3} {chi2(2):>5} {h:>3} {Tp:>4} {D:>4} {A6:>4} {B6:>4} "
              f"{C6:>4} {E4:>4} {F4:>4} {','.join(names)[:16]:>16}")


if __name__ == "__main__":
    main()
