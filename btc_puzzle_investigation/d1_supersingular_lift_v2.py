#!/usr/bin/env sage
# D1 (v2) — see d1_supersingular_lift_v1.py header. Fixes: place->divisor; factor-based order; BSGS dlog.
# The PLANT control is the canonicity validator: if dlog(d*R) != d, the RR-reduction is not canonical
# for this genus-3 curve and NO structure result is reported (tooling limit, stated honestly).
from sage.all import *
import math

def main():
    p = 43
    E = EllipticCurve(GF(p), [0, 7]); n = E.order()
    K = FunctionField(GF(p), 'x'); x = K.gen()
    Rt = PolynomialRing(K, 'T'); T = Rt.gen()
    L = K.extension(T**4 - (x**3 + 7), 'w'); w = L.gen()
    g = L.genus(); oo = L.places_infinite()[0]; oo_div = oo.divisor()
    Njac = L.L_polynomial()(1); Nan = Njac // E.order()
    print("p=%d n=%d genus=%d" % (p, n, g))
    print("V1  #Jac=%d = #E(%d)*#A_new(%d) ? %s" % (Njac, E.order(), Nan, E.order()*Nan == Njac))

    def reduce_class(D):                         # canonical-ish effective A ~ D + g*oo (deg g)
        V = (D + g*oo_div).basis_function_space()
        A = V[0].divisor() + D + g*oo_div
        return A
    def key(A):
        return tuple(sorted((repr(pl), m) for pl, m in A.list()))
    zero = reduce_class(0*oo_div)
    def add(A, B): return reduce_class(A + B - g*oo_div)
    def mul(A, m):
        Rr, base = zero, A
        while m > 0:
            if m & 1: Rr = add(Rr, base)
            base = add(base, base); m >>= 1
        return Rr

    def Qdivisor(d):
        P = d * E.gens()[0]
        if P.is_zero(): return None
        xp, yp = P.xy()
        if not yp.is_square(): return None
        wp = yp.sqrt()
        base = [b for b in (x - K(xp)).zeros() if b.degree() == 1][0]
        plus = minus = None
        for pl in L.places_above(base):
            if pl.degree() != 1: continue
            if (w - L(wp)).valuation(pl) > 0: plus = pl
            if (w + L(wp)).valuation(pl) > 0: minus = pl
        if plus is None or minus is None: return None
        return reduce_class(plus.divisor() - minus.divisor())

    d0 = next(d for d in range(1, n) if Qdivisor(d) is not None)
    R = Qdivisor(d0)
    print("base R=Q([%d]G)  R==0? %s" % (d0, key(R) == key(zero)))
    # order of R by factor test (1893 = 3*631)
    is3 = key(mul(R, 3)) == key(zero); is631 = key(mul(R, 631)) == key(zero)
    M = 1 if key(R) == key(zero) else (3 if is3 else (631 if is631 else 1893))
    print("V2  ord(R)=%d  divides #A_new? %s   closure key(M*R)==0:%s  key((M+1)R)==key(R):%s"
          % (M, Nan % M == 0, key(mul(R, M)) == key(zero), key(mul(R, M+1)) == key(R)))

    # BSGS dlog in <R> (order M)
    mstep = int(math.isqrt(M)) + 1
    baby = {}; cur = zero
    for j in range(mstep):
        baby[key(cur)] = j; cur = add(cur, R)
    negG = mul(R, (M - mstep) % M)
    def dlog(Q):
        c = Q
        for i in range(mstep + 1):
            if key(c) in baby: return (i*mstep + baby[key(c)]) % M
            c = add(c, negG)
        return None

    # V3 PLANT (canonicity validator): dlog(mul(R,d)) must == d
    plant_ok = all(dlog(mul(R, d % M)) == d % M for d in range(1, 12))
    print("V3  PLANT dlog(d*R)==d for d=1..11 : %s   <-- canonicity validator" % plant_ok)
    if not (M and Nan % M == 0 and plant_ok):
        print("VOID: reduction not validated (non-canonical RR reduction on this genus-3 curve).")
        print("      D1 needs a proper Jacobian (Khuri-Makdisi/Mumford); do NOT trust structure below.")
        return

    # liftable d, their dlogs, and the structure test with a RANDOM control
    liftable = [(d, Qdivisor(d)) for d in range(1, n)]
    ell = {}
    for d, Q in liftable:
        if Q is None: continue
        l = dlog(Q)
        if l is not None: ell[d] = l
    ds = sorted(ell)
    print("liftable & in <R>: %d of %d ;  E ordinary, A_new supersingular" % (len(ds), n-1))

    def best_affine(emap):                       # best (a,b): #{d: emap[d]==a*d+b mod M}, over all a
        from collections import Counter
        best = 0
        for a in range(M):
            c = Counter((emap[d] - a*d) % M for d in emap)
            best = max(best, c.most_common(1)[0][1])
        return best
    import random; random.seed(11)
    vals = list(ell.values()); random.shuffle(vals)
    rnd = {d: v for d, v in zip(ds, vals)}
    plant = {d: (d % M) for d in ds}
    print("STRUCTURE best-affine-fit (out of %d liftable):" % len(ds))
    print("   PLANT ell=d      : %d/%d (expect full)" % (best_affine(plant), len(ds)))
    print("   RANDOM shuffle    : %d/%d" % (best_affine(rnd), len(ds)))
    print("   REAL ell=dlogQ(d) : %d/%d" % (best_affine(ell), len(ds)))
    print("   ell_real:", {d: ell[d] for d in ds})
    print("READ: REAL near-full & >>RANDOM => structured lift (lever candidate advances);")
    print("      REAL ~ RANDOM => the supersingular factor is NOT reachable through this lift (scoped).")

main()
