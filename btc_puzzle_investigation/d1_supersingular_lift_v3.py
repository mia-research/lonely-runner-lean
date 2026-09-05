#!/usr/bin/env sage
# D1 (v3) = v2 with FLUSHED output + timing, so progress is visible and the cost is measured.
# Same committed validations: V1 #Jac=#E*#A_new ; V2 group closes ; V3 PLANT dlog(d*R)==d (canonicity).
# If V3 fails -> tooling limit, NOT a structure result.
from sage.all import *
import math, sys, time
def P(*a): print(*a); sys.stdout.flush()

p = 43
E = EllipticCurve(GF(p), [0, 7]); n = E.order()
K = FunctionField(GF(p), 'x'); x = K.gen()
Rt = PolynomialRing(K, 'T'); T = Rt.gen()
L = K.extension(T**4 - (x**3 + 7), 'w'); w = L.gen()
g = L.genus(); oo = L.places_infinite()[0]; oo_div = oo.divisor()
Njac = L.L_polynomial()(1); Nan = Njac // E.order()
P("p=%d n=%d genus=%d" % (p, n, g))
P("V1  #Jac=%d = #E(%d)*#A_new(%d) ? %s" % (Njac, E.order(), Nan, E.order()*Nan == Njac))

nred = [0]
def reduce_class(D):
    nred[0] += 1
    V = (D + g*oo_div).basis_function_space()
    return V[0].divisor() + D + g*oo_div
def key(A): return tuple(sorted((repr(pl), m) for pl, m in A.list()))
t0 = time.time(); zero = reduce_class(0*oo_div); t1 = time.time()
P("timing: one reduction = %.3f s" % (t1 - t0))
def add(A, B): return reduce_class(A + B - g*oo_div)
def mul(A, m):
    Rr, base = zero, A
    while m > 0:
        if m & 1: Rr = add(Rr, base)
        base = add(base, base); m >>= 1
    return Rr

def Qdiv(d):
    Pt = d * E.gens()[0]
    if Pt.is_zero(): return None
    xp, yp = Pt.xy()
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

d0 = next(d for d in range(1, n) if Qdiv(d) is not None)
R = Qdiv(d0); P("base R=Q([%d]G)  R==0? %s  (reductions so far %d)" % (d0, key(R)==key(zero), nred[0]))
t = time.time()
is3 = key(mul(R,3)) == key(zero); is631 = key(mul(R,631)) == key(zero)
M = 1 if key(R)==key(zero) else (3 if is3 else (631 if is631 else 1893))
P("V2  ord(R)=%d  divides #A_new? %s  [%.1fs, %d reductions]" % (M, Nan % M == 0, time.time()-t, nred[0]))
P("    closure key(M*R)==0: %s   key((M+1)R)==key(R): %s"
  % (key(mul(R,M))==key(zero), key(mul(R,M+1))==key(R)))

mstep = int(math.isqrt(M)) + 1
baby = {}; cur = zero
for j in range(mstep):
    baby[key(cur)] = j; cur = add(cur, R)
negG = mul(R, (M - mstep) % M)
P("BSGS table built (mstep=%d, reductions %d)" % (mstep, nred[0]))
def dlog(Q):
    c = Q
    for i in range(mstep + 1):
        k = key(c)
        if k in baby: return (i*mstep + baby[k]) % M
        c = add(c, negG)
    return None

plant_ok = all(dlog(mul(R, d % M)) == d % M for d in (1, 2, 5, 9))
P("V3  PLANT dlog(d*R)==d for d in {1,2,5,9}: %s   <-- CANONICITY VALIDATOR [%d reductions]"
  % (plant_ok, nred[0]))
if not (Nan % M == 0 and plant_ok):
    P("VOID: RR-reduction not canonical on this genus-3 curve -> D1 needs a proper Jacobian library.")
    P("      NO structure result reported.")
    sys.exit(0)

ell = {}
for d in range(1, n):
    Q = Qdiv(d)
    if Q is None: continue
    l = dlog(Q)
    if l is not None: ell[d] = l
ds = sorted(ell)
P("liftable & in <R>: %d of %d  [reductions %d]" % (len(ds), n-1, nred[0]))
def best_affine(em):
    from collections import Counter
    return max(Counter((em[d] - a*d) % M for d in em).most_common(1)[0][1] for a in range(M))
import random; random.seed(11)
vals = list(ell.values()); random.shuffle(vals)
rnd = {d: v for d, v in zip(ds, vals)}
P("STRUCTURE best-affine-fit out of %d:" % len(ds))
P("   PLANT ell=d       : %d" % best_affine({d: d % M for d in ds}))
P("   RANDOM shuffle    : %d" % best_affine(rnd))
P("   REAL  ell=dlogQ(d): %d" % best_affine(ell))
P("   ell_real: %s" % {d: ell[d] for d in ds})
