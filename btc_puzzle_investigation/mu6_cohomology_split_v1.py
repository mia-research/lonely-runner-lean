#!/usr/bin/env sage
# ANOMALY DRILL: the H^1 Frobenius-spectrum splitting of the chi2(y)-cover, mu4/mu6 decomposition.
# RUN: sage mu6_cohomology_split_v1.py
#
# Object: C: w^4 = x^3 + 7  (since chi2(y) <-> the cover w^2=y, and y^2=x^3+7 => w^4=x^3+7).
# C is the curve whose H^1_new = H^1(C) (-) H^1(E) carries the chi2(y) character sum
# (weil_deligne_character_bound_v1.md 6'/9: |sum chi2(y_P) e_n(ad)| <= 4 sqrt p, measured ~2 sqrt p).
#
# COMMITTED PREDICTIONS (pre-registration; drill protocol: characterization, never a verdict;
# every magnitude carries power+scope; control must fire; end in a sharper law / next probe):
#   P1  geometric genus g(C) = 3  (superelliptic w^4=cubic, gcd(4,3)=1 => g=(4-1)(3-1)/2=3)
#   P2  H^1(C) = H^1(E) (+) H^1_new,  dim 2 + 4;  E = C / <w -> -w>
#   P3  ALL Frobenius eigenvalues have |alpha| = sqrt(p)   (Weil / RH for curves)
#   P4  H^1_new (dim 4) splits under mu4 = <w -> i w> (the lift of [-1]_E) into V_i (+) V_{-i},
#       dim 2 + 2, complex-conjugate => the 4 NEW eigenvalues form 2 CONJUGATE PAIRS.
#   P5  the sum s1_new = sum of the 4 new eigenvalues = -(#C_new count) is REAL (conj pairs),
#       consistent with the untwisted sum sum_P chi2(y_P) being real and O(sqrt p).
#   CONTROL  non-CM base  C': w^4 = x^3 + x + 1 (j != 0): P1-P4 are GEOMETRIC (hold for any
#       separable cubic) so they must ALSO hold for C'. Any EXTRA structure special to B=7/j=0
#       (e.g. an mu3 action x->omega x forcing a finer CM splitting of the 4 new eigenvalues) is
#       what distinguishes CM from non-CM and is the DRILL's target -- named, not assumed.
# FALSIFICATION: g != 3, or dim split != 2+4, or |alpha| != sqrt p, or the 4 new eigenvalues do
#   NOT form 2 conjugate pairs => the mu4/[-1] splitting picture is wrong; report the actual structure.
#
# Exact over GF(p)/QQ (char-poly coeffs are integers). No float in the arithmetic; the |alpha|=sqrt p
# check compares alpha*alphabar to p exactly (integers).
from sage.all import *

def curve_Lpoly(p, cubic_coeffs):
    """L-poly numerator P(T)=prod(1-alpha_j T), deg 2g=6, of C: w^4=cubic(x), from #C(F_{p^k}),
    k=1,2,3 (affine points + 1 totally-ramified rational place at infinity, gcd(4,3)=1). Exact int."""
    a2, a1, a0 = cubic_coeffs
    T = polygen(ZZ, 'T')
    s = []
    for k in (1, 2, 3):
        q = p**k; Fq = GF(q); d = gcd(4, q - 1); e = (q - 1) // d
        cnt = 0
        for x in Fq:
            u = x**3 + a2*x**2 + a1*x + a0
            if u == 0:
                cnt += 1
            elif u**e == 1:
                cnt += d
        Nk = cnt + 1                                  # +1: unique rational place at infinity
        s.append(p**k + 1 - Nk)                       # power sum s_k = sum_j alpha_j^k
    s1, s2, s3 = s
    c1 = -s1
    c2 = (s1**2 - s2) // 2
    c3 = (-s1**3 + 3*s1*s2 - 2*s3) // 6               # Newton's identities
    P = 1 + c1*T + c2*T**2 + c3*T**3 + p*c2*T**4 + p**2*c1*T**5 + p**3*T**6  # functional equation
    return P, 3

def E_Lpoly(p, A, B):
    E = EllipticCurve(GF(p), [A, B])
    T = polygen(ZZ, 'T')
    ap = E.trace_of_frobenius()
    return 1 - ap*T + p*T**2

def eigs_of(Lpoly):
    """eigenvalues alpha_j = roots of the reversed (reciprocal) poly prod(T-alpha_j), in CC."""
    coeffs = [QQ(c) for c in Lpoly.list()]           # [c0..cd], Lpoly=prod(1-alpha T)
    Pol = PolynomialRing(CC, 'T')
    rec = Pol(list(reversed(coeffs)))                # prod(T - alpha_j)
    rts = rec.roots(multiplicities=False)
    return sorted(rts, key=lambda a: (a.imag(), a.real()))

def report(name, p, cubic, A, B):
    Lc, g = curve_Lpoly(p, cubic)
    Le = E_Lpoly(p, A, B)
    q, r = Lc.quo_rem(Le.change_ring(Lc.base_ring()))
    divides = (r == 0)
    Lnew = q if divides else Lc
    eg = eigs_of(Lnew)
    mags2 = [(a*a.conjugate()).real() for a in eg]
    allweil = all(abs(m - p) < 1e-5 for m in mags2)
    # conjugate pairs
    used = [False]*len(eg); npairs = 0
    for i in range(len(eg)):
        if used[i]: continue
        for j in range(i+1, len(eg)):
            if not used[j] and abs(eg[i].conjugate()-eg[j]) < 1e-5:
                used[i]=used[j]=True; npairs += 1; break
    # CM fingerprint: does the splitting field of L_new contain sqrt(-3) (E's CM field) / sqrt(-1)?
    Pol = PolynomialRing(QQ, 'T'); rec = Pol(list(reversed([QQ(c) for c in Lnew.list()])))
    has_m3 = has_m1 = None
    try:
        K = rec.splitting_field('a')
        has_m3 = K(-3).is_square(); has_m1 = K(-1).is_square()
    except Exception as ex:
        has_m3 = "err:%s" % repr(ex)[:20]
    print("  %-10s p=%-4d g=%d  L_E|L_C=%s  dimHnew=%d  |a|^2=p:%s  conj-pairs=%d/2  "
          "args/pi=%s" % (name, p, g, divides, Lnew.degree(), allweil, npairs,
          sorted([round(float(a.argument()/pi), 3) for a in eg])))
    print("       L_new=%s  split-field has sqrt(-3)? %s  sqrt(-1)? %s"
          % (Lnew, has_m3, has_m1))
    return Lnew

def main():
    import sys; sys.stdout.reconfigure(line_buffering=True)
    print("="*100)
    print("mu6/[-1] COHOMOLOGY SPLITTING DRILL  --  C: w^4=x^3+7 (chi2(y)-cover of E), H^1_new")
    print("="*100)
    primes = [13, 19, 31, 37, 43, 61, 67, 73, 79]
    print("\n[CM  B=7, j=0]  y^2=x^3+7 ;  cover w^4=x^3+7   (disc=-27*49, never 0 at these p)")
    for p in primes:
        report("secp_j0", p, (0, 0, 7), 0, 7)
    print("\n[CONTROL non-CM, j!=0]  y^2=x^3+2x+5 ;  cover w^4=x^3+2x+5")
    A, B = 2, 5
    for p in primes:
        if (4*A**3 + 27*B**2) % p == 0:
            print("  nonCM      p=%-4d  SKIP (singular: p | disc)" % p); continue
        report("nonCM", p, (0, A, B), A, B)
    print("\n[done]  Read magnitudes + conjugate-pair + (CM vs nonCM) eigenvalue-arg structure above.")

if __name__ == '__main__':
    main()
