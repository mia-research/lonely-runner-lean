#!/usr/bin/env sage
# RUN: sage supersingular_mu4_mechanism_v1.py
#
# N2 (frontier #11): is A_new supersingular at secp?  A_new = new part of Jac(C), C: w^4 = f(x),
# f a separable cubic, so w^2 = y, y^2 = f(x) = E.  Jac(C) ~ E x A_new, dim A_new = 2.
#
# The master's L2/P-A justifies "A_new ss <=> p = 3 mod 4" via "Q(i) inert" -- but retraction #18
# already says Q(i) is degree 2 acting on dim-2 A_new, so that is the WRONG reason (elliptic-curve
# criterion misapplied to a surface).  This script tests the CORRECT, scale-free mechanism:
#
#   mu4 automorphism  z4: (x,w) -> (x, i*w),  i = sqrt(-1).  For p = 3 mod 4, i not in F_p, so
#   Frobenius conjugates z4 -> z4^{-1}, hence Frob_p SWAPS the two 2-dim eigenspaces V_i <-> V_{-i}
#   of A_new = H^1_new.  Block-off-diagonal Frobenius  =>  char poly of Frob_p on A_new is EVEN:
#        char(t) = t^4 + c t^2 + p^2      (i.e. L_new = 1 + b1 T + b2 T^2 + p b1 T^3 + p^2 T^4 with b1 = 0).
#   This part uses ONLY p = 3 mod 4 + the order-4 automorphism -> it is scale-free, reaches secp.
#
# The residual for genuine supersingularity (all slopes 1/2, roots sqrt(p)*zeta): need also
#        b2 = p*m  with |m| <= 2   (Newton polygon single-slope 1/2, roots = sqrt(p)*root_of_unity).
#
# This script reports, exactly (integer point counts), for many primes x several cubics:
#   p mod 12 | CM? | b1 | b2 | b2/p | roots all sqrt(p)*zeta ?  (=> genuine ss)
# so we can see (i) whether b1 == 0 exactly for every p=3 mod 4 and every cubic, and
#              (ii) what m = b2/p is (which root-of-unity structure), and its dependence on p mod 3.

from sage.all import *

def L_new(p, cubic, A, B):
    """cubic = (a2,a1,a0) for f = x^3+a2 x^2+a1 x+a0; E: y^2 = f.
       L_new (deg 4, reciprocal) has 2 free coeffs => only F_p, F_{p^2} counts needed.
       a_{q}(C) = q+1-#C(F_q) = sum of the 6 Frobenius eigenvalues over F_p, raised to k for q=p^k
       gives the power sum P_k of A_new via  P_k = a_{p^k}(C) - a_{p^k}(E)."""
    a2, a1, a0 = cubic
    T = polygen(ZZ, 'T')
    aC = []                                  # a_{p^k}(C), k=1,2
    for k in (1, 2):
        q = p**k; Fq = GF(q); d = gcd(4, q - 1); e = (q - 1)//d; cnt = 0
        for x in Fq:
            u = x**3 + a2*x**2 + a1*x + a0
            cnt += 1 if u == 0 else (d if u**e == 1 else 0)
        aC.append(q + 1 - (cnt + 1))         # single point at infinity (gcd(4,3)=1)
    t = EllipticCurve(GF(p), [A, B]).trace_of_frobenius()
    aE1 = t; aE2 = t*t - 2*p                  # power sums of E's 2 eigenvalues
    P1 = aC[0] - aE1                          # power sums of A_new's 4 eigenvalues
    P2 = aC[1] - aE2
    e1 = P1; e2 = (P1*P1 - P2)//2             # elementary symmetric (Newton)
    b1 = -e1; b2 = e2                         # L_new = 1 - e1 T + e2 T^2 - p e1 T^3 + p^2 T^4
    return 1 + b1*T + b2*T**2 + p*b1*T**3 + p**2*T**4

def roots_are_sqrtp_zeta(Ln, p):
    """char poly of Frob = reverse of Ln; roots alpha have |alpha|=sqrt(p) by Weil.
       Supersingular <=> every alpha/sqrt(p) is a root of unity <=> alpha^2/p is a root of unity
       <=> (alpha^2) are p*(roots of unity).  Test via: are all roots of char(t) of the form
       sqrt(p)*zeta?  Equivalent decidable test: char(t^2=p*s) -> minimal poly of s is cyclotomic-ish;
       we test directly that char(t) | (t^{2N} - p^N)-type is overkill; instead check the surface
       Newton polygon is pure slope 1/2 AND |b2/p|<=2 with integrality, then confirm roots numerically
       lie on |z|=sqrt(p) and z/sqrt(p) is a root of unity."""
    b = Ln.list()                      # [1, b1, b2, p*b1, p^2]
    b1, b2 = b[1], b[2]
    # Frobenius char poly = t^4 * L_new(1/t) = t^4 + b1 t^3 + b2 t^2 + p b1 t + p^2
    R = polygen(QQbar, 't')
    char = R**4 + b1*R**3 + b2*R**2 + p*b1*R + p**2
    rts = char.roots(QQbar, multiplicities=False)
    ok = True
    for a in rts:
        z = a / QQbar(p).sqrt()
        # z is a root of unity iff |z|=1 and z is a root of some x^m-1; QQbar has is_root_of_unity via minpoly
        if not (abs(z) - 1).abs() < 1e-9:
            ok = False; break
        # test root-of-unity exactly: z algebraic, root of unity <=> its minimal polynomial is cyclotomic
        try:
            zru = z.is_root_of_unity()
        except AttributeError:
            # fallback: minimal polynomial divides x^m-1 for some m<=24
            mp = z.minpoly()
            zru = any((polygen(QQ,'x')**m - 1) % mp == 0 for m in range(1,25))
        if not zru:
            ok = False; break
    return ok, b1, b2

def main():
    import sys; sys.stdout.reconfigure(line_buffering=True)
    cubics = [
        ("CM  x^3+7",      (0,0,7),  0, 7),
        ("CM  x^3+2",      (0,0,2),  0, 2),
        ("CM  x^3+11",     (0,0,11), 0, 11),
        ("nCM x^3+2x+5",   (0,2,5),  2, 5),
        ("nCM x^3+x+1",    (0,1,1),  1, 1),
        ("nCM x^3-x+3",    (0,-1,3), -1, 3),
    ]
    primes = [p for p in prime_range(13, 200)]
    print("="*104)
    print("A_new = new part of Jac(w^4=f). L_new = 1 + b1 T + b2 T^2 + p b1 T^3 + p^2 T^4.")
    print("CLAIM(A): p=3 mod 4  =>  b1 = 0 EXACTLY (Frob swaps V_i<->V_{-i}), any cubic, scale-free.")
    print("CLAIM(B): p=3 mod 4  =>  b2 = p*m, |m|<=2  =>  roots sqrt(p)*zeta  =>  genuine supersingular.")
    print("="*104)
    print("  %-14s %-4s %-6s %6s %10s %8s  %-6s %-7s" %
          ("cubic","p","p%12","b1","b2","b2/p","ss?","rootsRU"))
    viol_b1 = []   # p=3mod4 with b1 != 0
    m_values = {}  # (cubic-type, p%3) -> set of m=b2/p at p=3mod4
    for lab, cub, A, B in cubics:
        for p in primes:
            if (4*A**3 + 27*B**2) % p == 0:      # singular reduction
                continue
            Ln = L_new(p, cub, A, B)
            if Ln is None:
                print("  %-14s %-4d %-6d  L_E does not divide L_C (skip)" % (lab, p, p%12)); continue
            ru_ok, b1, b2 = roots_are_sqrtp_zeta(Ln, p)
            bp = (b2 // p) if (b2 % p == 0) else None
            is_ss = (b2 % p == 0)
            print("  %-14s %-4d %-6d %6d %10d %8s  %-6s %-7s" %
                  (lab, p, p%12, b1, b2, str(bp) if bp is not None else "-",
                   "ss" if is_ss else "ORD", "yes" if ru_ok else "NO"))
            if p % 4 == 3:
                if b1 != 0:
                    viol_b1.append((lab,p,b1))
                key = ("CM" if lab.startswith("CM") else "nCM", p % 3)
                m_values.setdefault(key, set()).add(bp)
    print("="*104)
    print("CLAIM(A) check -- p=3 mod 4 rows with b1 != 0:", viol_b1 if viol_b1 else "NONE (b1==0 everywhere) [PASS]")
    print("CLAIM(B) check -- m = b2/p values seen at p=3 mod 4, by (curve-type, p mod 3):")
    for key in sorted(m_values):
        print("     %-6s p=%d mod3 :  m in %s" % (key[0], key[1], sorted(m_values[key])))
    print("[done]")

if __name__ == "__main__":
    main()
