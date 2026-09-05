from sage.schemes.cyclic_covers.constructor import CyclicCover

def frob(p, a):
    F = GF(p); R.<x> = PolynomialRing(F)
    return CyclicCover(4, x^3 + a).frobenius_polynomial()

def ell_frob(p, a):
    # Frobenius poly of E_a: y^2 = x^3 + a  (char poly of Frob, deg 2): T^2 - a_p T + p
    E = EllipticCurve(GF(p), [0, a])
    ap = E.trace_of_frobenius()
    T = polygen(ZZ)
    return T^2 - ap*T + p

for p in [43, 67, 127, 163]:
    print("="*70)
    print("p = %d   (p mod 12 = %d)" % (p, p%12))
    for a in [1,2,3,5,7,11]:
        if a % p == 0: continue
        T = polygen(ZZ)
        L6 = T^6*0  # placeholder
        Lf = frob(p,a)                      # deg 6, char poly of Frob on H^1
        Lf = Lf.change_ring(ZZ)
        Ef = ell_frob(p,a)                  # deg 2 elliptic part
        # new part = Lf / Ef  (should divide exactly)
        q, r = Lf.quo_rem(Ef)
        newpart = q
        exact = (r == 0)
        # cube the roots: build poly whose roots are alpha^3
        # over CC
        rootsCC = newpart.roots(CC, multiplicities=False)
        cubed = [ (z**3) for z in rootsCC ]
        # reconstruct integer poly with roots alpha^3 (deg 4)
        Rz.<z> = CC[]
        cubedpoly = prod(z - c for c in cubed)
        # round to integer coeffs
        coeffs = [c.real().round() for c in cubedpoly.list()]
        Zt = polygen(ZZ)
        cubed_int = sum(coeffs[i]*Zt^i for i in range(len(coeffs)))
        # is cubed_int a perfect square as a polynomial?
        fac = cubed_int.factor()
        is_sq = cubed_int.is_square()
        # also test: is newpart ITSELF (deg4, un-cubed, Frob^1) a square?
        newpart_sq = newpart.is_square()
        print("  a=%2d | new4(F_p) sq? %-5s | L^(3) new4 sq? %-5s | new4=%s" %
              (a, str(newpart_sq), str(is_sq), newpart if exact else "NONEXACT r=%s"%r))
        if is_sq:
            print("         L^(3) new4 = %s  = (%s)^2" % (cubed_int, cubed_int.sqrt()))
