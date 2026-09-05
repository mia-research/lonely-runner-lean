#!/usr/bin/env sage
"""reduce26_F_of_s1_v1.sage -- express F = y*iota(y) as a rational function of s1 = x+iota(x) in the
iota-fixed subfield L^<iota> = F_p(s1). Since both s1 and F are iota-invariant, F = P(s1)/Q(s1) for
polynomials P, Q. Find them by evaluating (s1, F) at many points of E and interpolating, EXACTLY over F_p.

Then form gF (g = branch quartic of E -> E/iota) and look for a factorization gF = h1 - h2 or a
special structure explaining Sum_t chi_2(gF) = const.
"""
from sage.all import GF, EllipticCurve, ZZ, PolynomialRing, FractionField


def iota_eval(p, A, B, xR, yR, x1, y1):
    """Evaluate iota(x), iota(y) at a point (x1,y1) on E over F_p (or F_{p^2})."""
    if x1 == xR: return None, None
    lam = (yR + y1) / (xR - x1)
    xiota = lam**2 - x1 - xR
    yiota = y1 + lam * (x1 - xiota)
    return xiota, yiota


if __name__ == "__main__":
    p, A, B = 43, 0, 7
    Fp = GF(p)
    E = EllipticCurve(Fp, [A, B]); n = E.order()
    G = next(P for P in E if P.order() == n)
    Rpt = 3*G; xR, yR = ZZ(Rpt[0]), ZZ(Rpt[1])
    print("p=%d R=[3]G=(%d,%d)" % (p, xR, yR))

    # collect (s1, F) pairs over E(F_p) points (not O, not the fixed points where x=iota(x))
    pts = []
    for P in E:
        if P.is_zero(): continue
        x1, y1 = ZZ(P[0]), ZZ(P[1])
        xi, yi = iota_eval(p, A, B, xR, yR, x1, y1)
        if xi is None: continue
        # is this a fixed point (x1 == xi)? skip -- s1 ill-behaved there
        if x1 == xi: continue
        s1 = (x1 + xi) % p
        Fval = (y1 * yi) % p
        pts.append((Fp(s1), Fp(Fval)))
    # how many distinct s1 values?
    s1vals = sorted(set(s for s,_ in pts))
    print("distinct s1 values:", len(s1vals))
    # F as a function of s1: for each s1, is F unique? (it must be, since F in F_p(s1))
    from collections import defaultdict
    by_s1 = defaultdict(set)
    for s, f in pts:
        by_s1[s].add(f)
    multi = {s:fs for s,fs in by_s1.items() if len(fs)>1}
    print("s1 values where F is NOT a function (multi-valued):", len(multi))
    if multi:
        for s, fs in list(multi.items())[:5]:
            print("   s1=%s -> F in %s" % (s, fs))
    # build the function s1 -> F (unique values only)
    func = {s: list(fs)[0] for s, fs in by_s1.items() if len(fs)==1}
    s1s = sorted(func.keys())
    Fs  = [func[s] for s in s1s]
    print("\ns1 -> F table (first 12):")
    for s, f in list(zip(s1s, Fs))[:12]:
        print("   s1=%3d -> F=%3d   chi_2(F)=%+d" % (s, f, 1 if f.is_square() and f!=0 else (-1 if not f.is_square() else 0)))

    # F is a rational function of s1 over F_p. Since we have the full table on F_p-points, fit
    # F = P(s1)/Q(s1) by rational interpolation. Use sage's rational_reconstruction / interpolate.
    # Simpler: F is a FUNCTION F_p -> F_p (where defined); test if it agrees with a low-degree poly mod (s1^p - s1).
    # The relation F = P(s1)/Q(s1): find P, Q with deg small. Try F*Q(s1) = P(s1), solve linear.
    Ppoly = PolynomialRing(Fp, 'S'); S = Ppoly.gen()
    for dQ in range(0, 6):
        for dP in range(0, 8):
            # unknowns: P coeffs (dP+1) and Q coeffs (dQ+1, Q monic wlog or Q[0]=1)
            # F * Q(s1) = P(s1) at each s1 in func. Linear system.
            # Q = sum_{j} q_j S^j , P = sum_i p_i S^i. F(s1)*sum q_j s1^j = sum p_i s1^i.
            # unknowns q_j (j=0..dQ) and p_i (i=0..dP). Set q_0 = 1 (fix scale). Equations per s1.
            import itertools
            nunk = (dP+1) + dQ   # p_0..p_dP, q_1..q_dQ
            rows = []; rhs = []
            for s1 in s1s:
                f = func[s1]
                row = []
                # coeff of p_i: s1^i
                for i in range(dP+1): row.append(int(s1)**i % p)
                # coeff of q_j (j=1..dQ): -f * s1^j  (move F*Q to LHS: F*sum q_j s1^j - sum p_i s1^i = 0)
                for j in range(1, dQ+1): row.append((-int(f)*int(s1)**j) % p)
                rows.append(row); rhs.append(int(f) % p)  # q_0=1 => F*1 term on RHS... let me redo:
            # equation: F*(1 + sum_{j>=1} q_j s1^j) = sum_i p_i s1^i
            #   => sum_i p_i s1^i  -  F*sum_{j>=1} q_j s1^j  =  F
            rows = []; rhs = []
            for s1 in s1s:
                f = int(func[s1])
                row = []
                for i in range(dP+1): row.append(int(s1)**i % p)
                for j in range(1, dQ+1): row.append((-f*int(s1)**j) % p)
                rows.append(row); rhs.append(f % p)
            # solve over F_p
            M = Ppoly.base()  # Fp
            from sage.all import Matrix, vector
            try:
                Ms = Matrix(Fp, rows); vb = vector(Fp, rhs)
                sol = Ms.solve_right(vb)
            except Exception:
                continue
            # check on ALL s1s (including those not used -- here we used all, so just verify fit)
            pco = list(sol[:dP+1]); qco = [Fp(1)] + list(sol[dP+1:])
            Pp = sum(c*S**i for i,c in enumerate(pco)); Qp = sum(c*S**j for j,c in enumerate(qco))
            # verify Qp != 0 and F = P/Q at every s1 in func
            ok = all(Qp(s1) != 0 and Pp(s1)/Qp(s1) == func[s1] for s1 in s1s)
            if ok and dQ >= 1:
                print("\n*** F(s1) = (%s)/(%s)   [deg P=%d, deg Q=%d] ***" % (Pp, Qp, dP, dQ))
                break
        else:
            continue
        break
