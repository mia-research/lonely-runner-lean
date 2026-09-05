#!/usr/bin/env sage
# ============================================================================================
# D1 — is the non-homomorphic lift Q(P)=[P+ - P-] in A_new = Prym(C/E) a STRUCTURED function of d?
# (C: w^4=x^3+7, E: y^2=x^3+7, A_new supersingular at p=7 mod12; the "supersingular cover lever".)
#
# The lever needs ell(d) := dlog_{A_new}(Q([d]G)) to be an efficiently-structured function of d.
# Hom(E,A_new)=0 => ell is NOT linear; test whether it is OTHERWISE structured, vs pseudo-random.
#
# INSTRUMENT VALIDATION (must all pass or the run is VOID — printed, for scrutiny):
#   V1  #Jac(C)=#E*#A_new  (L-polynomial vs class-group order)
#   V2  the class-group reduction closes: <R> has order dividing #A_new, and A_m + A_k = A_{m+k}
#   V3  CONTROL-PLANT: with ell_planted(d)=d (i.e. class = d*R), the structure test DETECTS linearity
#   V4  CONTROL-RANDOM: ell(random class) reads UNSTRUCTURED
# Only if V1-V4 pass is the REAL ell(d)=dlog(Q([d]G)) structure test reportable.
# Exact throughout (divisor arithmetic over F_p; principality via Riemann-Roch dimension).
# ============================================================================================
from sage.all import *

def build(p):
    E = EllipticCurve(GF(p), [0, 7]); n = E.order()
    K = FunctionField(GF(p), 'x'); x = K.gen()
    Rt = PolynomialRing(K, 'T'); T = Rt.gen()
    L = K.extension(T**4 - (x**3 + 7), 'w'); w = L.gen()
    g = L.genus()
    oo = L.places_infinite()
    assert len(oo) == 1 and oo[0].degree() == 1, "need one rational place at infinity"
    return E, n, K, L, w, g, oo[0]

def lift_places(L, K, x, w, xp, wp):
    """the two degree-1 places of C above x=xp with w=+wp and w=-wp (require y_P=wp^2 a QR)."""
    base = (x - K(xp)).zeros()
    base = [b for b in base if b.degree() == 1][0]
    out = {}
    for pl in L.places_above(base):
        if pl.degree() != 1: continue
        res = w.evaluate(pl)                       # residue of w at the degree-1 place, in F_p
        out[res] = pl
    return out                                      # dict {wp: place, -wp: place}

def main():
    p = 43
    E, n, K, L, w, g, oo = build(p)
    x = K.gen()
    print("p=%d n=#E=%d genus=%d" % (p, n, g))
    Lp = L.L_polynomial(); Njac = Lp(1); Nan = Njac // E.order()
    print("V1  #Jac=%d  #E=%d  #A_new=%d   #E*#A_new==#Jac : %s"
          % (Njac, E.order(), Nan, E.order() * Nan == Njac))

    # ---- class-group reduction relative to oo (canonical effective A ~ D + g*oo, deg g) ----
    def reduce_class(D):
        V = (D + g * oo).basis_function_space()
        f = V[0]
        A = f.divisor() + D + g * oo
        assert A.degree() == g and all(m >= 0 for _, m in A.list()), "reduction not effective"
        return A
    def key(A):
        return tuple(sorted((repr(pl), m) for pl, m in A.list()))
    def add(A, B):                                   # class [A-g oo] + [B-g oo]
        return reduce_class(A + B - g * oo)
    zero = reduce_class(0 * oo)                       # identity class, A = g*oo

    # a base class R in A_new: use Q of the first liftable d
    def Qclass(d):
        P = d * E.gens()[0]
        if P.is_zero(): return None
        xp, yp = P.xy()
        if not yp.is_square(): return None            # not liftable (P+,P- irrational)
        wp = yp.sqrt()
        pls = lift_places(L, K, x, w, xp, wp)
        if wp not in pls or (-wp) not in pls: return None
        return reduce_class(pls[wp].divisor() - pls[-wp].divisor())

    # find a liftable d for the base R
    d0 = next(d for d in range(1, n) if Qclass(d) is not None)
    R = Qclass(d0)
    print("base R = Q([%d]G); R==identity? %s" % (d0, key(R) == key(zero)))

    # V2: build <R>, check order | #A_new and group closes
    table = {key(zero): 0}; cur = zero; order = None
    for m in range(1, Nan + 1):
        cur = add(cur, R); k = key(cur)
        if k in table:
            order = m; break
        table[k] = m
    print("V2  ord(R)=%s   divides #A_new(%d)? %s   |<R>|=%d"
          % (order, Nan, (order is not None and Nan % order == 0), len(table)))
    # closure spot-check: 5*R via add equals table entry 5
    chk = zero
    for _ in range(5): chk = add(chk, R)
    print("    closure check key(5R)==table-index-5: %s" % (table.get(key(chk)) == 5))

    def dlog(A):
        return table.get(key(A))                      # None if A not in <R>

    # ---- V3 PLANT + V4 RANDOM + REAL, all through the SAME structure test ----
    def structure_score(ell_map):
        """ell_map: dict d->ell in Z/order. Score = best linear (a*d+b) fit rate over Z/order,
           and 'determines d mod 3' (fiber purity). Compared to random baseline by caller."""
        ds = sorted(ell_map); vals = [ell_map[d] for d in ds]
        best = 0
        for a in range(order):
            # b chosen to maximize matches for this a (mode of ell-a*d)
            from collections import Counter
            c = Counter((ell_map[d] - a * d) % order for d in ds)
            best = max(best, c.most_common(1)[0][1])
        return best, len(ds)                          # best affine-fit count out of len(ds)

    if order is None:
        print("VOID: R does not generate a cyclic group covering itself; need 2-gen dlog. STOP.")
        return
    # liftable d and their Q-classes
    liftable = [(d, Qclass(d)) for d in range(1, n)]
    liftable = [(d, Q) for d, Q in liftable if Q is not None and dlog(Q) is not None]
    covered = [d for d, Q in liftable]
    ell_real = {d: dlog(Q) for d, Q in liftable}
    print("liftable & in <R>: %d of %d" % (len(covered), n - 1))

    # PLANT: ell(d) = d mod order  (i.e., class = d*R). Must score = full (perfectly affine).
    ell_plant = {d: (d % order) for d in covered}
    bp, npp = structure_score(ell_plant)
    # RANDOM: shuffle real ell values across d
    import random; random.seed(7)
    vals = list(ell_real.values()); random.shuffle(vals)
    ell_rand = {d: v for d, v in zip(covered, vals)}
    br, nr = structure_score(ell_rand)
    # REAL
    breal, nreal = structure_score(ell_real)
    print("V3 PLANT   best-affine-fit %d/%d  (expect = %d, full)" % (bp, npp, npp))
    print("V4 RANDOM  best-affine-fit %d/%d" % (br, nr))
    print("REAL       best-affine-fit %d/%d   ell(d)=dlog(Q([d]G))" % (breal, nreal))
    print("           (REAL >> RANDOM and near full => structured lift = lever; REAL ~ RANDOM => no lever via this map)")
    print("ell_real sample:", {d: ell_real[d] for d in covered[:8]})

if __name__ == "__main__":
    main()
