#!/usr/bin/env sage
# H^1_new(C: w^4=x^3+B) -- SEPARATING three distinct structures, each with its own scope.
# RUN: sage mu6_cohomology_split_v3.py
#
# v1 drifted to an overclaim ("7 mod 12 => sqrt(p) zeta_6 = a CM fingerprint"); the v1 CONTROL
# refutes that reading. v2 then over-corrected into a DISMISSAL ("supersingular degeneracy
# contaminates the signal") -- the negative-bias failure the project memory names. v3 follows the
# anomaly to its LAW instead. Three separate objects, three separate scopes:
#
#  L1 (EXACT CONSERVATION, elementary, scope = p mod 4, curve-INDEPENDENT):
#      p = 3 mod 4  =>  chi2(-1) = -1  =>  chi2(y_{-P}) = chi2(-y_P) = -chi2(y_P), so the involution
#      [-1] pairs P with -P and  SUM_{P in E(F_p)} chi2(y_P) = 0  EXACTLY (2-torsion gives chi2(0)=0).
#      p = 1 mod 4 => chi2(y) is EVEN in P, no cancellation, sum generically nonzero.
#      This is the ENFORCING SYMMETRY of L2 below -- not "degeneracy".
#  L2 (GEOMETRIC, scope = any cubic):  zeta4:(x,w)->(x,i w) in Aut(C), zeta4^2 = (w->-w), E=C/<zeta4^2>,
#      so H^1_new = (zeta4^2=-1)-eigenspace, zeta4 = +-i on it (the 2+2 split) => Q(i) c End^0(A_new).
#      Hence A_new SUPERSINGULAR iff p inert in Q(i) iff p = 3 mod 4.  L1 is its elementary shadow.
#  L3 (CM, scope = cubic x^3+B <=> j(E)=0):  additionally zeta3:(x,w)->(omega x, w) => mu12 c Aut(C),
#      Q(zeta12) c End^0(A_new), A_new a CM ABELIAN SURFACE. Clean test at ORDINARY primes (where L1/L2
#      do NOT force vanishing): does L_new split completely over Q(zeta12)?
#
# COMMITTED PREDICTIONS (before data):
#   P-A  ordinary <=> p = 1 mod 4, BOTH covers                              (tests L2)
#   P-D  SUM chi2(y_P) = 0 EXACTLY  <=>  p = 3 mod 4, BOTH covers           (tests L1)
#   P-B  at ORDINARY primes L_new splits/Q(zeta12) for CM cover; not for non-CM  (tests L3)
#   P-E  at SUPERSINGULAR primes: characterize the root-of-unity order m of alpha^2/p -- REPORTED as a
#        structure with its scope, NOT dismissed. (v1's zeta6-only reading was too narrow, not "noise".)
# FALSIFICATION: any row violating P-A/P-D, or CM failing / non-CM passing P-B systematically.
# Exact integer arithmetic for sums/point counts; CC only to read eigenvalue arguments.
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

def chi2_sums(p, A, B):
    """EXACT integer sums over E(F_p): SUM chi2(y_P), SUM chi2(x_P)  (P != O)."""
    E = EllipticCurve(GF(p), [A, B]); Sy = 0; Sx = 0
    for P in E.points():
        if P.is_zero(): continue
        y = ZZ(P[1]); x = ZZ(P[0])
        Sy += (0 if y % p == 0 else (1 if pow(y, (p-1)//2, p) == 1 else -1))
        Sx += (0 if x % p == 0 else (1 if pow(x, (p-1)//2, p) == 1 else -1))
    return Sy, Sx

def rootorder(z, maxm=48):
    for m in range(1, maxm+1):
        if abs(z**m - 1) < 1e-6: return m
    return None

def analyze(name, p, cubic, A, B, K12):
    Ln = L_new_of(p, cubic, A, B)
    if Ln is None:
        print("  %-6s p=%-4d  *** L_E does not divide L_C ***" % (name, p)); return None
    c2 = Ln.list()[2]; ordinary = (c2 % p != 0)
    Pol = PolynomialRing(CC, 'T'); rec = Pol(list(reversed([QQ(c) for c in Ln.list()])))
    rts = rec.roots(multiplicities=False)
    weil = all(abs((a*a.conjugate()).real() - p) < 1e-5 for a in rts)
    Sy, Sx = chi2_sums(p, A, B)
    P_ = PolynomialRing(K12, 'T'); rc = P_(list(reversed([K12(c) for c in Ln.list()])))
    sp12 = all(f.degree() == 1 for f, _ in rc.factor())
    m = None
    if not ordinary:                                   # supersingular: alpha^2/p is a root of unity
        m = rootorder(CC(rts[0]**2 / p))
    print("  %-6s p=%-4d p%%4=%d p%%12=%-2d %-4s Weil:%s  Sy=%-5d Sx=%-5d  splitQ(z12):%-5s  ord(a^2/p)=%s"
          % (name, p, p % 4, p % 12, "ORD" if ordinary else "ss", weil, Sy, Sx, sp12, m))
    return dict(p=p, ordinary=ordinary, Sy=Sy, sp12=sp12, m=m)

def main():
    import sys; sys.stdout.reconfigure(line_buffering=True)
    K12 = CyclotomicField(12)
    primes = [p for p in prime_range(10, 112) if p % 3 == 1]
    print("="*118)
    print("H^1_new STRUCTURE v3 -- L1 exact conservation (p mod4) | L2 geometric Q(i) | L3 CM Q(zeta12)")
    print("="*118)
    print("\n[CM  j=0]  E: y^2=x^3+7 ,  cover C: w^4=x^3+7")
    rA = [analyze("CM", p, (0,0,7), 0, 7, K12) for p in primes]
    print("\n[non-CM control]  E: y^2=x^3+2x+5 ,  cover C: w^4=x^3+2x+5")
    A, B = 2, 5
    rB = [analyze("nonCM", p, (0,A,B), A, B, K12) for p in primes if (4*A**3+27*B**2) % p != 0]

    print("\n" + "="*118 + "\nFALSIFICATION CHECK")
    for rows, lab in ((rA, "CM"), (rB, "nonCM")):
        rows = [r for r in rows if r]
        pa = all(r['ordinary'] == (r['p'] % 4 == 1) for r in rows)
        pd = all((r['Sy'] == 0) == (r['p'] % 4 == 3) for r in rows)
        orow = [r for r in rows if r['ordinary']]
        nsp = sum(1 for r in orow if r['sp12'])
        ms = sorted(set(r['m'] for r in rows if not r['ordinary']))
        print("  %-6s  P-A ordinary<=>p=1mod4 : %-5s  (%d primes)" % (lab, pa, len(rows)))
        print("          P-D  Sy==0 <=> p=3mod4 : %-5s   <-- EXACT conservation law L1" % pd)
        print("          P-B  splits/Q(z12) at ORDINARY p : %d/%d" % (nsp, len(orow)))
        print("          P-E  supersingular orders ord(alpha^2/p) observed: %s" % ms)
    print("\n[done]")

if __name__ == '__main__':
    main()
