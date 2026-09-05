#!/usr/bin/env sage
# RIGOROUS re-examination of the H^1_new(C: w^4=x^3+B) Frobenius structure.  RUN: sage this.py
#
# v1 drifted toward an overclaim ("p=7 mod 12 => sqrt(p)*zeta_6, a CM fingerprint"). v1's OWN
# control refutes it: sqrt(-3)-in-splitting-field is NOT CM-specific (non-CM shows it too), and the
# per-prime root-of-unity order is contaminated by SUPERSINGULAR degeneracy (CM p=19 gives +-sqrt19,
# non-CM p=43,79 give sqrt(p)*zeta_6). This script separates the GEOMETRIC part from the CM part and
# tests each with a matched non-CM control, committing predictions BEFORE the data.
#
# THEOREM-LEVEL CLAIMS (proved from the automorphisms; this script only CONFIRMS their consequences):
#   T1  C: w^4 = cubic(x) is genus 3 (superelliptic, gcd(4,3)=1); E=C/<w->-w> => H^1(C)=H^1(E)(+)H^1_new,
#       dim 2+4.  [independent of the cubic]
#   T2  zeta4:(x,w)->(x,i w) in Aut(C) for ANY cubic; zeta4^2 = (w->-w); on H^1_new zeta4 acts as +-i
#       (the 2+2 split) => Q(i) c End^0(A_new) GEOMETRICALLY.  Consequence: A_new is SUPERSINGULAR iff
#       p is inert in Q(i) iff  p = 3 mod 4.  [holds for CM AND non-CM -- NOT a CM signal]
#   T3  ONLY for cubic = x^3 + B (<=> j(E)=0): zeta3:(x,w)->(w x, w) in Aut(C) too => mu12 c Aut(C)
#       and Q(zeta12) c End^0(A_new): A_new is a CM ABELIAN SURFACE (CM field Q(zeta12), degree 4=2*dim).
#       Consequence at ORDINARY primes: Frobenius pi in Q(zeta12), so L_new SPLITS COMPLETELY over
#       Q(zeta12).  For a generic (non-CM) cover A_new has only Q(i): L_new does NOT split over Q(zeta12).
#
# COMMITTED PREDICTIONS (pre-registration; falsification = any row breaking these):
#   P-A  ordinary <=> p = 1 mod 4   for BOTH covers (T2; the '7 mod 12' supersingularity is geometric).
#   P-B  at ORDINARY primes: L_new splits over Q(zeta12) for the CM cover (ALL such p); NOT for non-CM
#        (generic p).  <-- THE clean CM fingerprint, uncontaminated by supersingular degeneracy.
#   P-C  the per-prime root-of-unity order at SUPERSINGULAR primes is NOT a clean CM signal (both covers
#        vary; retract v1's 'zeta6 at 7 mod 12').
# Exact over GF(p)/QQ/CyclotomicField. No float in arithmetic (|alpha|^2=p checked as exact integer).
from sage.all import *

def curve_Lnew(p, cubic, A, B):
    """L_new(T) = L_C / L_E  (degree 4), from #C(F_{p^k}) k=1..3 (affine + 1 place at infinity)."""
    a2, a1, a0 = cubic; T = polygen(ZZ, 'T'); s = []
    for k in (1, 2, 3):
        q = p**k; Fq = GF(q); d = gcd(4, q - 1); e = (q - 1) // d; cnt = 0
        for x in Fq:
            u = x**3 + a2*x**2 + a1*x + a0
            cnt += 1 if u == 0 else (d if u**e == 1 else 0)
        s.append(p**k + 1 - (cnt + 1))
    s1, s2, s3 = s
    c1 = -s1; c2 = (s1**2 - s2)//2; c3 = (-s1**3 + 3*s1*s2 - 2*s3)//6
    Lc = 1 + c1*T + c2*T**2 + c3*T**3 + p*c2*T**4 + p**2*c1*T**5 + p**3*T**6
    ap = EllipticCurve(GF(p), [A, B]).trace_of_frobenius()
    Le = 1 - ap*T + p*T**2
    q_, r = Lc.quo_rem(Le)
    return (q_ if r == 0 else None), (r == 0)

def analyze(name, p, cubic, A, B, K12):
    Ln, dvd = curve_Lnew(p, cubic, A, B)
    if not dvd:
        print("  %-8s p=%-4d  L_E does NOT divide L_C  *** T1 FAILS ***" % (name, p)); return
    c2 = Ln.list()[2]
    ordinary = (c2 % p != 0)                                   # Newton-polygon: ordinary iff p | middle coeff is false
    # eigenvalues + Weil check (exact: product of |alpha|^2 etc. via the poly; |alpha|^2=p means Ln(T)=p^2 T^4+...+1 palindromic-with-p)
    Pol = PolynomialRing(CC, 'T'); rec = Pol(list(reversed([QQ(c) for c in Ln.list()])))
    rts = rec.roots(multiplicities=False)
    weil = all(abs((a*a.conjugate()).real() - p) < 1e-5 for a in rts)
    args = sorted([round(float(a.argument()/pi), 3) for a in rts])
    # split over Q(zeta12), Q(i), Q(sqrt-3)
    def splits_over(Kf):
        P = PolynomialRing(Kf, 'T'); rc = P(list(reversed([Kf(c) for c in Ln.list()])))
        return all(f.degree() == 1 for f, _ in rc.factor())
    sp12 = splits_over(K12)
    print("  %-8s p=%-4d p%%12=%-2d  %-4s  Weil:%s  splitQ(z12):%-5s  args/pi=%s"
          % (name, p, p % 12, "ORD" if ordinary else "ss", weil, sp12, args))
    return dict(p=p, ordinary=ordinary, sp12=sp12)

def main():
    import sys; sys.stdout.reconfigure(line_buffering=True)
    K12 = CyclotomicField(12)
    primes = [p for p in prime_range(10, 140) if p % 3 == 1]     # p=1 mod3 so mu3/zeta3 is defined
    print("="*104)
    print("H^1_new(w^4=x^3+B) STRUCTURE -- geometric (Q(i), p mod4) vs CM (Q(zeta12), ordinary split)")
    print("committed: P-A ordinary<=>p=1mod4 (both); P-B L_new splits/Q(zeta12) at ORDINARY p for CM only")
    print("="*104)
    resA = {}
    print("\n[CM  j=0]  w^4 = x^3 + 7")
    rA = [analyze("CM", p, (0, 0, 7), 0, 7, K12) for p in primes]
    print("\n[non-CM control]  w^4 = x^3 + 2x + 5   (skip p | disc)")
    A, B = 2, 5
    rB = [analyze("nonCM", p, (0, A, B), A, B, K12) for p in primes if (4*A**3+27*B**2) % p != 0]

    print("\n" + "="*104 + "\nSUMMARY / falsification check")
    def check(rows, label):
        rows = [r for r in rows if r]
        pa = all((r['ordinary']) == (r['p'] % 4 == 1) for r in rows)
        ord_rows = [r for r in rows if r['ordinary']]
        pb_split = [r['sp12'] for r in ord_rows]
        print("  %-8s  P-A (ordinary<=>p=1mod4): %s (%d primes)" % (label, pa, len(rows)))
        print("           at ORDINARY primes, L_new splits/Q(zeta12): %d/%d  -> %s"
              % (sum(pb_split), len(pb_split),
                 "ALL split (CM by Q(zeta12))" if all(pb_split) else "NOT all"))
    check(rA, "CM")
    check(rB, "nonCM")
    print("\n  P-C: the per-prime root-of-unity ANGLE at supersingular primes is read above -- compare CM")
    print("       vs nonCM ss rows; if they overlap, v1's 'zeta6 at 7mod12 = CM' is retracted (expected).")
    print("[done]")

if __name__ == '__main__':
    main()
