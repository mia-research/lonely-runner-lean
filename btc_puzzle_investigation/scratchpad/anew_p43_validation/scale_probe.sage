# R1 de-risk: does Sage's genus-3 Jac GROUP LAW (what build_S needs) scale past p=43
# WITHOUT the O(|A_new|) dlog table? Time places-enum + one build_S per prime, alarm-bounded.
import signal, time
class TO(Exception): pass
def _to(s,f): raise TO()
signal.signal(signal.SIGALRM, _to)

def try_prime(p, budget=90):
    signal.alarm(budget)
    t0 = time.time()
    try:
        Fp = GF(p); B = 7
        Kf.<x> = FunctionField(Fp); Rr.<T> = Kf[]
        L.<w> = Kf.extension(T^4 - (x^3 + B))
        J = L.jacobian(model='hess'); G0 = J.group()
        E = EllipticCurve(Fp, [0, B]); G = E.gens()[0]; nE = Integer(G.order())
        beta = None
        for c in Fp:
            if c != 1 and c^3 == 1: beta = c; break
        b2 = beta^2
        t_setup = time.time() - t0
        t1 = time.time()
        finite = [pl for pl in L.places(1) if not pl.is_infinite_place()]
        coord = {(Fp(x.evaluate(pl)), Fp(w.evaluate(pl))): pl for pl in finite}
        t_places = time.time() - t1
        def lift(P):
            if P.is_zero(): return None
            xP, yP = Fp(P[0]), Fp(P[1])
            if not yP.is_square(): return None
            r = yP.sqrt(); a = coord.get((xP, r)); b = coord.get((xP, -r))
            return None if (a is None or b is None) else G0.point(a.divisor() - b.divisor())
        phi = lambda P: E(beta*P[0], P[1]); phi2 = lambda P: E(b2*P[0], P[1])
        def build_S(P):
            Q0, Q1, Q2 = lift(P), lift(phi(P)), lift(phi2(P))
            if None in (Q0, Q1, Q2): return None
            return Q0 + Integer(b2)*Q1 + Integer(beta)*Q2
        # first rational-lift d
        d0 = next((d for d in range(1, nE) if Fp((d*G)[1]).is_square()), None)
        t2 = time.time()
        S = build_S(d0*G)
        t_build = time.time() - t2
        ordS = Integer(S.order()) if S is not None else None
        # one scalar-mult (torsion projection style): [ (p^2+p+1)//3 ] * S
        anew = p*p + p + 1
        t3 = time.time()
        _ = Integer(anew//3) * S if S is not None else None
        t_scalar = time.time() - t3
        signal.alarm(0)
        print("p=%-5d OK  |A_new|=%d ordS=%s | setup=%.2fs places(%d)=%.2fs build_S=%.2fs scalarmult=%.2fs"
              % (p, anew, ordS, t_setup, len(finite), t_places, t_build, t_scalar), flush=True)
        return True
    except TO:
        signal.alarm(0)
        print("p=%-5d HANG (> %ds) after %.1fs" % (p, budget, time.time()-t0), flush=True)
        return False
    except Exception as ex:
        signal.alarm(0)
        print("p=%-5d ERR %s: %s" % (p, type(ex).__name__, str(ex)[:80]), flush=True)
        return False

# ladder of p == 7 mod 12 (j=0, p==3 mod4 & 1 mod3)
for p in [43, 79, 127, 199, 211, 331, 499, 691, 1009, 2011, 3011]:
    if not try_prime(p, budget=90):
        print("  -> stopping ladder at first hang/err", flush=True); break
