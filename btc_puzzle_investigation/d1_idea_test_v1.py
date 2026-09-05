#!/usr/bin/env sage
# TEST THE IDEA, not just the affine method.
# Claim under test: P=[d]G  --lift-->  Q(d) in Jac(C), C: w^4 = x^3+7 (supersingular A_new),
#   internal DLP is easy, so an isotypic projection of Q(d) recovers bits of d.
#
# The ONLY efficient way an "easy internal DLP" recovers d is a GROUP HOMOMORPHISM
# (that is exactly what MOV/Frey-Ruck are). So the idea lives or dies on how close
# d |-> Q(d) is to additive. We test additivity at four levels, hardest-to-kill last:
#   (0) raw additivity                Q(a)+Q(b) = Q(a+b)                 [Hom=0 predicts fail]
#   (1) affine (lever)                Q(a)+Q(c) = 2Q(b),  a+c=2b         [affine ell => recovers d]
#   (2) additive-up-to-small-torsion  order of the defect delta=Q(a)+Q(b)-Q(a+b)
#          -- if every defect is killed by a small k, then k*Q IS additive and leaks d mod n/gcd.
#          This is the strongest form of the spec's "isotypic projection kills the defect" hope.
#   (3) congruence leak               does d mod m sort the images (the spec's "d mod 3" criterion)?
#
# Everything exact (finite-field / divisor arithmetic). No floats in the signal path.
from sage.all import *
import sys
def P(*a): print(*a); sys.stdout.flush()

def curve_ok(p):
    E = EllipticCurve(GF(p), [0,7]); n = E.order()
    return n if is_prime(n) else None

def run(p, order_cap=60, tri_cap=40):
    n = curve_ok(p)
    if n is None:
        P("p=%d  order not prime, skipped" % p); return
    E = EllipticCurve(GF(p), [0,7]); G = E.gens()[0]
    K = FunctionField(GF(p), 'x'); x = K.gen()
    Rt = PolynomialRing(K, 'T'); T = Rt.gen()
    L = K.extension(T**4 - (x**3 + 7), 'w'); w = L.gen()
    g = L.genus()
    P("\n=== p=%d  n=%d  p mod 12=%d  genus=%d ===" % (p, n, p % 12, g))

    def Qdiv(d):
        Pt = d*G
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
        return plus.divisor() - minus.divisor()

    def principal(D): return D.degree() == 0 and D.dimension() >= 1
    def order_of(D, cap):
        acc = 0*D
        for k in range(1, cap+1):
            acc = acc + D
            if principal(acc): return k
        return None  # > cap

    Q = {}
    for d in range(1, n):
        q = Qdiv(d)
        if q is not None: Q[d] = q
    lift = sorted(Q)
    P("liftable d (y a QR): %d of %d" % (len(lift), n-1))
    if len(lift) < 6:
        P("  too few lifts, skipping structural tests"); return

    # CONTROLS (must fire)
    P("CONTROL+ div(w) principal? %s  (must be True)" % principal(w.divisor()))
    P("CONTROL- Q(%d) principal?  %s  (must be False)" % (lift[0], principal(Q[lift[0]])))

    # (0) raw additivity
    tri = [(a,b) for a in lift for b in lift if a < b and (a+b) % n in Q][:200]
    ok0 = sum(1 for a,b in tri if principal(Q[a]+Q[b]-Q[(a+b)%n]))
    P("(0) additivity   Q(a)+Q(b)=Q(a+b) : %d/%d" % (ok0, len(tri)))

    # (1) affine lever
    trp = [(a,b,c) for a in lift for b in lift for c in lift if a < c and a+c == 2*b][:200]
    ok1 = sum(1 for a,b,c in trp if principal(Q[a]+Q[c]-2*Q[b]))
    P("(1) affine lever Q(a)+Q(c)=2Q(b) : %d/%d" % (ok1, len(trp)))

    # (2) order of the non-additivity defect: is the lift additive up to SMALL torsion?
    #     if every defect dies at small k, k*Q is a homomorphism and leaks d.
    defect_orders = []
    for (a,b) in tri[:tri_cap]:
        s = (a+b) % n
        D = Q[a] + Q[b] - Q[s]
        if principal(D):
            defect_orders.append(1); continue
        o = order_of(D, order_cap)
        defect_orders.append(o if o is not None else ('>%d' % order_cap))
    finite = [o for o in defect_orders if isinstance(o, int)]
    beyond = sum(1 for o in defect_orders if not isinstance(o, int))
    P("(2) defect orders (smallest k: k*(Q(a)+Q(b)-Q(a+b)) principal), cap=%d:" % order_cap)
    P("     sampled %d defects | order<=cap: %d | order>cap: %d" %
      (len(defect_orders), len(finite), beyond))
    if finite:
        P("     min=%d  max=%d  distinct small orders=%s" %
          (min(finite), max(finite), sorted(set(finite))[:12]))
    P("     READ: a single common small k killing ALL defects => a real lever. "
      "large/varied orders => none.")

    # (3) congruence leak: does d mod m sort the images? test if  Q(a)-Q(b) principal
    #     correlates with (a==b mod m). principal(Q(a)-Q(b)) means same class.
    for m in (2, 3):
        same_cls_within = same_cls_across = tot_within = tot_across = 0
        pairs = [(a,b) for a in lift for b in lift if a < b][:400]
        for a,b in pairs:
            same = principal(Q[a]-Q[b])
            if (a % m) == (b % m):
                tot_within += 1; same_cls_within += int(same)
            else:
                tot_across += 1; same_cls_across += int(same)
        P("(3) d mod %d : same-class rate within=%d/%d  across=%d/%d "
          "(leak => within >> across)" %
          (m, same_cls_within, tot_within, same_cls_across, tot_across))

for p in (43, 79, 127, 163):
    run(p)
P("\nDONE.")
