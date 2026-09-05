from sage.schemes.cyclic_covers.constructor import CyclicCover

def newpart(p, a):
    F = GF(p); R.<x> = PolynomialRing(F)
    Lf = CyclicCover(4, x^3 + a).frobenius_polynomial().change_ring(ZZ)
    E = EllipticCurve(GF(p), [0, a]); ap = E.trace_of_frobenius()
    T = Lf.parent().gen()
    Ef = T^2 - ap*T + p
    q, r = Lf.quo_rem(Ef)
    return q, (r==0)

def classify(p):
    # For each unit a, is the deg-4 new part supersingular (roots = sqrt(p)*root_of_unity)?
    # Test: does L^(3) new part become a perfect square for ALL a?  and at which power?
    results = {}
    saw_ss = False; saw_ordinary=False
    for a in range(1, min(p, 40)):
        if a % p == 0: continue
        np4, exact = newpart(p, a)
        if not exact: 
            results[a]=('nonexact',); continue
        # cube roots
        rc = np4.roots(CC, multiplicities=False)
        cubed = prod( (polygen(CC) - z**3) for z in rc)
        ci = [c.real().round() for c in cubed.list()]
        Zt=polygen(ZZ); cp = sum(ci[i]*Zt^i for i in range(len(ci)))
        sq1 = np4.is_square()
        sq3 = cp.is_square()
        # supersingular test: all |roots|^2 = p and roots are sqrt(p)*(root of unity)?
        # equivalently every root alpha satisfies alpha/sqrt(p) is a root of unity -> alpha^24 = p^12 etc
        # cheap proxy: is some power alpha^m real scalar? test alpha^12 == p^6 ?
        ss = all( abs((z**12) - p**6) < 1e-6*p**6 for z in rc)
        results[a] = (sq1, sq3, ss)
        if ss: saw_ss=True
        else: saw_ordinary=True
    frac_sq3 = sum(1 for v in results.values() if len(v)==3 and v[1]) / len([v for v in results.values() if len(v)==3])
    return saw_ss, saw_ordinary, frac_sq3

print("p mod12 | anySS | anyOrdinary | frac(a: L^(3)new is square)")
for p in [13,37,61,73,97,   19,31,43,67,79,103,127,139,151,163,   7,199,211,   5,11,17,23,29,41,53,59,71,83]:
    if not is_prime(p): continue
    try:
        ss,ordn,f = classify(p)
        print("p=%4d  (%2d)  | SS=%-5s | Ord=%-5s | frac_sq3=%.3f" % (p, p%12, ss, ordn, f))
    except Exception as e:
        print("p=%4d  ERR %s" % (p, str(e)[:50]))
