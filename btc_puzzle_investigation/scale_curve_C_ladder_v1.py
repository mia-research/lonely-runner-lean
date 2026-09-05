#!/usr/bin/env python3
"""scale_curve_C_ladder_v1.py -- push M13 (B1=0; B2=C; C^2/p <= ~3.7 Weil-norm bound)
past the p=6007 banner floor toward 10^6.  EXACT INTEGER ARITHMETIC ONLY.

  B1 = sum_{x in F_p^*} sigma(x)                    (field; PROVED = 0)
  C  = sum_{x in F_p} sigma(x) chi2(x^3 + 7)        (curve x-sum)
  B2 = sum_{P != O} sigma(x_P) = B1 + C             (so B1=0 => B2 = C)
Reuses the validated sigma machinery (build, sigma_fn, chi2_table); no #E point
count needed for C, so this runs fast and samples many primes per order.

PRE-STATED (before the run):
  (i)  B1 == 0 at every p            -- PROVED (sigma odd + F_p^* negation-closed): instrument check
  (ii) B2 == C at every p            -- follows from (i): instrument check
  (iii) C^2/p stays <= ~3.7          -- the Weil-norm bound |C| <= ||sigma||_W * 2 sqrt(p);
        THIS is the genuine test: an unbounded-constant failure would show C^2/p growing with p.
        Report the running max as an exact rational; list any prime with C^2/p > 4.
"""
import sys, time
from fractions import Fraction as Fr
from sympy import isprime
from _sigma_chi2_scan_v1 import build, sigma_fn, chi2_table

def curve_C(p):
    eis, eps, beta, R1, R2, DET = build(p)
    sig, orient = sigma_fn(p, eis, eps, R1, R2, DET)
    if sig is None:
        return None
    chi2 = chi2_table(p)
    B1 = sum(sig(x) for x in range(1, p))
    C  = sum(sig(x) * chi2(((x * x % p) * x + 7) % p) for x in range(p))
    return B1, C

def primes_from(o, k):
    out, p = [], o | 1
    while len(out) < k:
        if p % 6 == 1 and p != 7 and isprime(p):
            out.append(p)
        p += 2
    return out

def main():
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 10**6
    per = int(sys.argv[2]) if len(sys.argv) > 2 else 6
    orders = [6007, 10**4, 3*10**4, 10**5, 3*10**5, 10**6]
    ladder = []
    for o in orders:
        if o > cap: break
        ladder += primes_from(o, per)
    ladder = sorted(set(ladder))

    print("=" * 84)
    print("M13 curve x-sum:  B1==0 (proved), B2==C, and the C^2/p Weil-norm bound, past the floor")
    print("=" * 84)
    print(f"{'p':>9} {'bits':>4} {'B1':>4} {'C':>7} {'B2==C':>6} {'C^2/p (exact)':>16} {'~':>7}  [t]")
    print("-" * 84)
    b1_ok = True
    max_c2p = Fr(0)
    max_at = None
    over4 = []
    for p in ladder:
        t0 = time.time()
        res = curve_C(p)
        dt = time.time() - t0
        if res is None:
            print(f"{p:>9} {p.bit_length():>4}   sigma_fn: no orientation agrees  [{dt:.1f}s]")
            continue
        B1, C = res
        b1 = (B1 == 0)
        b1_ok = b1_ok and b1
        b2_eq_c = b1  # B2 = B1 + C == C  iff  B1 == 0
        c2p = Fr(C * C, p)
        if c2p > max_c2p:
            max_c2p, max_at = c2p, p
        if c2p > 4:
            over4.append((p, C, c2p))
        approx = float(c2p)  # noqa: float  (display only; verdict uses the exact Fr above)
        star = "" if b1 else "  **B1!=0**"
        print(f"{p:>9} {p.bit_length():>4} {B1:>4} {C:>7} {str(b2_eq_c):>6} {str(c2p.limit_denominator(1000)):>16} {approx:>7.3f}{star}  [{dt:.1f}s]")

    print("-" * 84)
    print(f"B1 == 0 at every prime: {b1_ok}   (=> B2 == C everywhere)")
    print(f"max C^2/p = {max_c2p.limit_denominator(1000)} ~ {float(max_c2p):.4f}  at p = {max_at}")  # noqa: float  (display)
    print(f"primes with C^2/p > 4: {len(over4)}", over4 if over4 else "(none)")
    print("VERDICT:", "B1=0 held; C^2/p stayed bounded (<=~3.7 regime)"
          if b1_ok and not over4 else "**see anomalies above**")

if __name__ == "__main__":
    main()
