#!/usr/bin/env sage
# CORRECTED CM discriminator.  RUN: sage mu6_cohomology_split_v4.py
#
# v3's P-B ("L_new splits over Q(zeta12)") was a BADLY DESIGNED test and is retracted as a
# discriminator: if the roots already lie in Q(i) c Q(zeta12) the test passes TRIVIALLY, so it cannot
# separate Q(i)-multiplication (geometric, every cover has it via zeta4) from Q(zeta12)-CM (only j=0).
# Non-CM passed it 5/6 -- exactly the trivial-pass failure mode.
#
# CORRECTED PREDICTION (committed before this run):
#   at ORDINARY primes (p = 1 mod 4, where no vanishing/supersingular degeneracy is forced):
#     CM cover   (Q(zeta12)-CM, degree 4 = 2*dim, pi generates the full CM field):
#                 splits/Q(i) = FALSE ,  splits/Q(sqrt-3) = FALSE ,  splits/Q(zeta12) = TRUE
#     non-CM     (only Q(i) from zeta4):
#                 splits/Q(i) = TRUE  (=> its Q(zeta12) pass is trivial)
#   FALSIFICATION: CM splitting over Q(i), or non-CM failing Q(i), at ordinary primes.
# Also re-reports the supersingular order table with explicit sample sizes (an OBSERVATION, not a law).
from sage.all import *

def L_new_of(p, cubic, A, B):
    a2, a1, a0 = cubic; T = polygen(ZZ, 'T'); s = []
    for k in (1, 2, 3):
        q = p**k; Fq = GF(q); d = gcd(4, q - 1); e = (q - 1)//d; cnt = 0
        for x in Fq:
            u = x**3 + a2*x**2 + a1*x + a0
            cnt += 1 if u == 0 else (d if u**e == 1 else 0)
        s.append(p**k + 1 - (cnt + 1))
    s1, s2, s3 = s
    c1 = -s1; c2 = (s1**2 - s2)//2; c3 = (-s1**3 + 3*s1*s2 - 2*s3)//6
    Lc = 1 + c1*T + c2*T**2 + c3*T**3 + p*c2*T**4 + p**2*c1*T**5 + p**3*T**6
    Le = 1 - EllipticCurve(GF(p), [A, B]).trace_of_frobenius()*T + p*T**2
    q_, r = Lc.quo_rem(Le)
    return (q_ if r == 0 else None)

def splits_over(Ln, Kf):
    P = PolynomialRing(Kf, 'T')
    rc = P(list(reversed([Kf(c) for c in Ln.list()])))
    return all(f.degree() == 1 for f, _ in rc.factor())

def main():
    import sys; sys.stdout.reconfigure(line_buffering=True)
    Qi = QuadraticField(-1, 'i'); Qm3 = QuadraticField(-3, 'r3'); K12 = CyclotomicField(12)
    primes = [p for p in prime_range(10, 112) if p % 3 == 1]
    print("="*104)
    print("CORRECTED CM DISCRIMINATOR -- split over Q(i) is the real test (Q(zeta12) passes trivially)")
    print("="*104)
    print("  %-6s %-5s %-4s  %-12s %-14s %-14s" % ("curve", "p", "type", "split/Q(i)", "split/Q(sqrt-3)", "split/Q(zeta12)"))
    summary = {}
    for lab, cubic, A, B in (("CM", (0, 0, 7), 0, 7), ("nonCM", (0, 2, 5), 2, 5)):
        rows = []
        for p in primes:
            if (4*A**3 + 27*B**2) % p == 0:
                continue
            Ln = L_new_of(p, cubic, A, B)
            if Ln is None:
                continue
            c2 = Ln.list()[2]; ordinary = (c2 % p != 0)
            si, s3, s12 = splits_over(Ln, Qi), splits_over(Ln, Qm3), splits_over(Ln, K12)
            print("  %-6s %-5d %-4s  %-12s %-14s %-14s"
                  % (lab, p, "ORD" if ordinary else "ss", si, s3, s12))
            rows.append((p, ordinary, si, s3, s12))
        summary[lab] = rows
    print("\n" + "="*104 + "\nFALSIFICATION CHECK (ORDINARY primes only -- the uncontaminated regime)")
    for lab in ("CM", "nonCM"):
        orow = [r for r in summary[lab] if r[1]]
        ni = sum(1 for r in orow if r[2]); n3 = sum(1 for r in orow if r[3]); n12 = sum(1 for r in orow if r[4])
        print("  %-6s  ordinary primes=%d :  split/Q(i)=%d  split/Q(sqrt-3)=%d  split/Q(zeta12)=%d"
              % (lab, len(orow), ni, n3, n12))
    print("\n  Reading: CM should be  Q(i)=0, Q(sqrt-3)=0, Q(zeta12)=all  (pi generates the full quartic CM field).")
    print("           nonCM should be Q(i)=all  (=> its Q(zeta12) pass is trivial, not evidence of CM).")
    print("[done]")

if __name__ == '__main__':
    main()
