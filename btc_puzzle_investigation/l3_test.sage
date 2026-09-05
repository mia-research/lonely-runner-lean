# Object-level test of the "L^(3) is a perfect square" claim for C_a: w^4 = x^3 + a
# Build the genus-3 L-polynomial over F_p by point counting over F_{p^k}, k=1,2,3,
# factor out the elliptic quotient E_a: y^2 = x^3+a, examine the degree-4 "new" part,
# then cube Frobenius (base change to F_{p^3}) and test perfect-square-ness.

def curve_points_over(p, k, a):
    F = GF(p**k, 'g')
    aa = F(a)
    cnt = 0
    # affine points w^4 = x^3 + a  ; for each x, number of w with w^4 = c
    # count 4th roots of c in F
    for x in F:
        c = x**3 + aa
        if c == 0:
            cnt += 1  # w=0
        else:
            # number of solutions w^4 = c  = number of w
            # = #{w : w^4 = c}; compute via: c is a d-th power where d=gcd(4,q-1)
            q = p**k
            d = gcd(4, q-1)
            if c**((q-1)//d) == 1:
                cnt += d
            else:
                cnt += 0
    # points at infinity: model w^4 = x^3+a is a plane-ish curve; use smooth model count
    # Instead, use the L-poly from #C via a clean route below with Sage's own curve.
    return cnt

def Lpoly_via_sage(p, a):
    # Use Sage superelliptic / cyclic cover if available
    from sage.all import GF, PolynomialRing
    F = GF(p)
    R.<x> = PolynomialRing(F)
    try:
        from sage.schemes.cyclic_covers.constructor import CyclicCover
        C = CyclicCover(4, x^3 + a)
        return C.frobenius_polynomial()
    except Exception as e:
        return ('ERR', str(e))

for p in [43, 67, 127, 163]:
    for a in [1, 2, 3, 5, 7]:
        if a % p == 0: 
            continue
        Lp = Lpoly_via_sage(p, a)
        print("p=%d a=%d :" % (p,a), Lp)
    print("----")
