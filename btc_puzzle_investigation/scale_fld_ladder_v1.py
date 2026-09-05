#!/usr/bin/env python3
"""scale_fld_ladder_v1.py -- push the FIELD-LATTICE FLD laws (M11, M12) 2-3 orders
past the p=6007 banner floor, toward ~10^6.  EXACT INTEGER ARITHMETIC ONLY.

Object: FLD(p) = sum_{x in F_p} sigma(x) chi2(x)  = <sigma, chi2>_FIELD.
Reuses the VALIDATED sigma / eis / lift machinery from _sigma_chi2_scan_v1
(build, sigma_fn, chi2_table); FLD needs no #E point-count and no n-prime filter.

PRE-STATED PREDICTION (write it down BEFORE the run; the run only confirms/breaks):
  (A) p == 1 mod 4                      => FLD = 0            (forced; M12)
  (B) p == 7 mod 24 (== 7 mod8, 1 mod3) => FLD = 0            (UNFORCED zero; M12, was 35/35)
  (C) p == 19 mod 24 (==3 mod8, 1 mod3) => FLD != 0 and |FLD| = 6*h(-p)   (M11, modulo lemma L1)
Grade: (A) is proved-forced -> instrument check.  (B),(C) are the genuine tests;
(C) tests the L1-dependent identity -- it is NOT guaranteed to pass (that is the point).
Any MISS is listed individually (drill rule: reproduce the count, name the misses).
"""
import sys, time
from fractions import Fraction as Fr
from sympy import isprime
from _sigma_chi2_scan_v1 import build, sigma_fn, chi2_table

# ---------- exact class number h(-p) of Q(sqrt(-p)), p == 3 mod 4 (disc = -p) ----------
def class_number_disc(p):
    """h(-p) for p prime == 3 mod 4  (fundamental discriminant D = -p).
    Count of reduced primitive forms (a,b,c): b^2 - 4ac = D, -a < b <= a <= c,
    b >= 0 if (a==c or a==b).  Exact integer arithmetic."""
    assert p % 4 == 3
    D = -p
    h = 0
    a = 1
    while a * a * 3 <= -D:          # a <= sqrt(|D|/3)
        # b has parity of D and |b| <= a
        b = -a + ((a + (D & 1)) % 2)   # smallest b > -a with b == D (mod 2)
        b = -a
        while (b - D) % 2 != 0:        # enforce b == D mod 2
            b += 1
        while b <= a:
            four_ac = b * b - D        # = 4 a c
            if four_ac % (4 * a) == 0:
                c = four_ac // (4 * a)
                if c >= a:
                    from math import gcd
                    g = gcd(gcd(abs(a), abs(b)), abs(c))
                    if g == 1:
                        if (a == c or a == b):
                            if b >= 0:
                                h += 1
                        elif -a < b:
                            h += 1
            b += 2
        a += 1
    return h

# ---------- FLD via the validated sigma machinery (no n-prime gate) ----------
def fld_of(p):
    eis, eps, beta, R1, R2, DET = build(p)
    sig, orient = sigma_fn(p, eis, eps, R1, R2, DET)
    if sig is None:
        return None, None
    chi2 = chi2_table(p)
    FLD = sum(sig(x) * chi2(x) for x in range(p))
    return FLD, orient

# ---------- prime pickers ----------
def near_prime_res(target, r, m):
    """nearest prime >= target with p == r (mod m)."""
    p = target + ((r - target) % m)
    while not isprime(p):
        p += m
    return p

def main():
    # ladder: at each order pick one p == 7 mod24 (unforced zero) and one == 19 mod24 (class-no law)
    orders = [10**3, 6007, 10**4, 3*10**4, 10**5, 3*10**5, 10**6]
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 10**6
    ladder = []
    for o in orders:
        if o > cap: break
        ladder.append(near_prime_res(o, 7, 24))    # class B: predict FLD = 0
        ladder.append(near_prime_res(o, 19, 24))    # class C: predict |FLD| = 6 h(-p)
    # also a p == 1 mod 4 instrument check per order (class A: forced zero)
    for o in [6007, 10**4, 10**5]:
        if o <= cap:
            ladder.append(near_prime_res(o, 13, 24))   # 13 mod24 -> 1 mod4, 1 mod3
    ladder = sorted(set(ladder))

    print("=" * 96)
    print("FLD field-lattice laws (M11 |FLD|=6h(-p); M12 unforced zero) -- ladder past the banner floor")
    print("=" * 96)
    print(f"{'p':>9} {'bits':>4} {'p%24':>4} {'class':>5} {'FLD':>7} {'6h(-p)':>8} {'predict':>16} {'verdict':>8}  [t]")
    print("-" * 96)

    misses, checks = [], 0
    for p in ladder:
        t0 = time.time()
        FLD, orient = fld_of(p)
        dt = time.time() - t0
        if FLD is None:
            print(f"{p:>9} {p.bit_length():>4} {p%24:>4}   ---  sigma_fn: no orientation agrees with eps  [{dt:.1f}s]")
            continue
        r24 = p % 24
        if p % 4 == 1:
            cls, pred, ok = "A", "FLD==0 (forced)", (FLD == 0)
            h6 = ""
        elif r24 == 7:
            cls, pred, ok = "B", "FLD==0 (unforced)", (FLD == 0)
            h6 = ""
        elif r24 == 19:
            h = class_number_disc(p)
            h6 = 6 * h
            cls, pred, ok = "C", "|FLD|==6h(-p)", (abs(FLD) == 6 * h)
        else:
            cls, pred, ok = "?", "(other)", None
            h6 = ""
        checks += 1 if ok is not None else 0
        verdict = "OK" if ok else ("**MISS**" if ok is False else "-")
        if ok is False:
            misses.append((p, r24, cls, FLD, h6))
        print(f"{p:>9} {p.bit_length():>4} {r24:>4} {cls:>5} {FLD:>7} {str(h6):>8} {pred:>16} {verdict:>8}  [{dt:.1f}s]")

    print("-" * 96)
    print(f"checks with a prediction: {checks}   misses: {len(misses)}")
    for m in misses:
        print(f"  MISS p={m[0]} (p%24={m[1]}, class {m[2]}): FLD={m[3]}, 6h={m[4]}")
    print("VERDICT:", "ALL PREDICTIONS HELD" if not misses else "**A PREDICTION BROKE -- see misses**")
    # instrument cross-check: h(-163) == 1 (classic)
    print("instrument: h(-163) =", class_number_disc(163), "(expect 1)")
    print("            h(-23)  =", class_number_disc(23),  "(expect 3)")
    print("            h(-47)  =", class_number_disc(47),  "(expect 5)")

if __name__ == "__main__":
    main()
