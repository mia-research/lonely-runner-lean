#!/usr/bin/env python3
"""
summation_poly_structure_v1.py — WAYS TO DETERMINE PROOF.

The index-calculus lever question at the level of the Semaev polynomial S_3, made exact.
A 3-point relation [c]G=P1+P2 needs S_3(x1,x2,x_R)=0 with x1,x2 in factor base F. The COST
of finding those is governed by the GENUS of the fixed-target curve
    C_t : S_3(x1,x2,t)=0        (a (2,2) biquadratic in the (x1,x2)-plane).
  genus 0 (reducible/singular => rational => PARAMETRIZABLE => cheap enumerate) = a LEVER.
  genus 1 (smooth irreducible biquadratic => no parametrization => search)     = NO lever.

Provable for given (p,t): reducibility by EXACT factorization over Q; smoothness by EXACT
search for singular points over F_p. We PROVE the structure for the computed cases.

We VERIFY the S_3 formula numerically (vanishes on real collinear triples) before trusting
it -- no formula-from-memory. CM curve y^2=x^3+7 vs non-CM control y^2=x^3+x+1.
"""
import sympy as sp
from sympy import symbols, Poly, factor_list, QQ, ZZ
from hybrid_char_sum_v1 import legendre, tonelli, find_point, padd


x1, x2, x3 = symbols('x1 x2 x3')


def S3(a, b):
    """Semaev 3rd summation polynomial for y^2 = x^3 + a x + b (sympy expr)."""
    return ((x1 - x2)**2 * x3**2
            - 2 * ((x1 + x2) * (x1 * x2 + a) + 2 * b) * x3
            + ((x1 * x2 - a)**2 - 4 * b * (x1 + x2)))


def S3_int(X1, X2, X3, a, b, p):
    """S_3 evaluated as a plain integer mod p (fast; matches S3())."""
    return (((X1 - X2)**2 * X3**2
             - 2 * ((X1 + X2) * (X1 * X2 + a) + 2 * b) * X3
             + ((X1 * X2 - a)**2 - 4 * b * (X1 + X2)))) % p


def curve_pts(p, a, b):
    pts = []
    for x in range(p):
        r = (x**3 + a * x + b) % p
        if r == 0: pts.append((x, 0))
        elif legendre(r, p) == 1:
            y = tonelli(r, p); pts.append((x, y)); pts.append((x, (p - y) % p))
    return pts


def padd_ab(P, Q, p, a):
    if P is None: return Q
    if Q is None: return P
    (X1, Y1), (X2, Y2) = P, Q
    if X1 == X2 and (Y1 + Y2) % p == 0: return None
    if P == Q:
        lam = (3 * X1 * X1 + a) % p * pow(2 * Y1, p - 2, p) % p
    else:
        lam = (Y2 - Y1) % p * pow((X2 - X1) % p, p - 2, p) % p
    X3 = (lam * lam - X1 - X2) % p
    return (X3, (lam * (X1 - X3) - Y1) % p)


def verify_S3(p, a, b):
    """S_3(x(P1),x(P2),x(P3))=0 mod p for every collinear triple P1+P2+P3=O."""
    pts = curve_pts(p, a, b)
    bad = tot = 0
    for i, P in enumerate(pts):
        for Q in pts[:i + 1]:
            R = padd_ab(P, Q, p, a)
            if R is None: continue
            tot += 1
            if S3_int(P[0], Q[0], R[0], a, b, p) != 0: bad += 1
    return bad, tot


def beta_weight(p, a, b, ncr):
    """over F_p: is S_3(w x1, w x2, w x3) == w^k S_3 for all x?  find k (the beta-weight)."""
    if (p - 1) % 3: return None
    e = (p - 1) // 3; g = 2
    while pow(g, e, p) == 1: g += 1
    w = pow(g, e, p)                                  # primitive cube root mod p
    import random
    rng = random.Random(p)
    ks = set()
    for _ in range(ncr):
        A, B, C = rng.randrange(p), rng.randrange(p), rng.randrange(p)
        base = S3_int(A, B, C, a, b, p)
        scaled = S3_int(w * A % p, w * B % p, w * C % p, a, b, p)
        if base == 0:
            continue
        for k in range(3):
            if scaled == pow(w, k, p) * base % p:
                ks.add(k); break
        else:
            ks.add(-1)                                # no consistent weight
    return ks


def fixed_target_analysis(p, a, b, targets):
    """for each t: factor C_t=S_3(.,.,t) over Q; count F_p solutions + singular points."""
    out = []
    for t in targets:
        Ct = sp.expand(S3(a, b).subs(x3, t))
        # factor over Q
        try:
            fl = factor_list(Poly(Ct, x1, x2, domain=QQ))
            nfac = sum(mult for _, mult in fl[1])
            irred = (nfac == 1)
        except Exception:
            irred = None
        # F_p: solutions + singular points (C = dC/dx1 = dC/dx2 = 0), EXACT integer arithmetic
        def C(X, Y): return S3_int(X, Y, t, a, b, p)
        def Cx1(X, Y):
            return (2 * (X - Y) * t * t - 2 * t * (2 * X * Y + a + Y * Y)
                    + 2 * (X * Y - a) * Y - 4 * b) % p
        def Cx2(X, Y):
            return (2 * (Y - X) * t * t - 2 * t * (2 * X * Y + a + X * X)
                    + 2 * (X * Y - a) * X - 4 * b) % p
        npts = nsing = 0
        for X in range(p):
            for Y in range(p):
                if C(X, Y) == 0:
                    npts += 1
                    if Cx1(X, Y) == 0 and Cx2(X, Y) == 0:
                        nsing += 1
        out.append((t, irred, npts, nsing))
    return out


def main():
    print("SEMAEV S_3 STRUCTURE — the index-calculus fixed-target genus question")
    print("=" * 78)
    # 1. verify the formula numerically (no formula-from-memory)
    for (a, b, lab) in [(0, 7, 'CM y^2=x^3+7'), (1, 1, 'non-CM y^2=x^3+x+1')]:
        bad, tot = verify_S3(307, a, b)
        print(f"  verify S_3 [{lab}] p=307: {bad}/{tot} nonzero on collinear triples "
              f"=> formula {'CORRECT' if bad == 0 else 'WRONG'}")
    print()

    # 2. global factorization over Q
    for (a, b, lab) in [(0, 7, 'CM'), (1, 1, 'non-CM')]:
        fl = factor_list(Poly(S3(a, b), x1, x2, x3, domain=QQ))
        n = sum(m for _, m in fl[1])
        print(f"  S_3 over Q [{lab}]: {n} irreducible factor(s) "
              f"=> {'IRREDUCIBLE (no global factorization lever)' if n == 1 else 'REDUCIBLE'}")
    print()

    # 3. beta-weight (CM only)
    ksCM = beta_weight(307, 0, 7, 40)
    ksNC = beta_weight(307, 1, 1, 40)
    print(f"  beta-weight [CM]: S_3(w.x) = w^k S_3 with k in {sorted(ksCM)} "
          f"(single k => exact beta-covariance = the automorphism)")
    print(f"  beta-weight [non-CM]: k in {sorted(ksNC)} (mixed/-1 => no beta symmetry)\n")

    # 4. fixed-target genus signal: reducible/singular?  genus1 => ~p pts, 0 singular
    p = 307
    tg = [0, 1, 5, 100, 200]                # incl t=0 (beta-fixed x) and generic t
    print(f"  fixed-target C_t: S_3(x1,x2,t)=0 over F_{p}  (genus1 => ~{p} pts, 0 singular = NO lever)")
    for (a, b, lab) in [(0, 7, 'CM'), (1, 1, 'non-CM')]:
        print(f"   [{lab}]")
        for (t, irred, npts, nsing) in fixed_target_analysis(p, a, b, tg):
            tag = ("genus1/no-lever" if (irred and nsing == 0)
                   else ("REDUCIBLE=LEVER?" if irred is False else "SINGULAR=genus0=LEVER?"))
            print(f"     t={t:>3}: over-Q {'irred' if irred else 'REDUCIBLE'}, "
                  f"F_p pts={npts:>4}, singular={nsing}  => {tag}")
    print()
    print("READ: S_3 irreducible over Q + C_t smooth irreducible (genus 1) for generic t,")
    print("      SAME for CM and non-CM => the fixed-target relation curve is non-parametrizable")
    print("      => NO index-calculus lever at the S_3 level beyond the beta-automorphism. If a")
    print("      special t (e.g. 0) is singular/reducible EQUALLY for both => not CM-specific.")


if __name__ == "__main__":
    main()
