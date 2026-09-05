#!/usr/bin/env sage
# anew_sorder_sweep_v1.sage — the S-visibility map: for each p = 7 mod 12, the multiset of
# S([d]G) ORDERS on the QR half (no dlog table — just .order()), vs M = p^2+p+1 factored.
# Output: anew_sorder_sweep.json + stdout. Lightweight: ~(|QR| order computations)/prime.
import json, sys, time
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")

PRIMES = [1303, 1831, 2143, 2647]
out = {}
for p in PRIMES:
    t0 = time.time()
    B = 7
    Fp = GF(p)
    K.<x> = FunctionField(Fp); R.<T> = K[]
    L.<w> = K.extension(T^4 - (x^3 + B))
    J = L.jacobian(model='hess'); G0 = J.group()
    E = EllipticCurve(Fp, [0, B])
    Gp = E.gens()[0]
    beta = None
    for c in range(2, p):
        if pow(c, 3, p) == 1 and c != 1:
            beta = c; break
    b2 = beta^2 % p
    finite = [pl for pl in L.places(1) if not pl.is_infinite_place()]
    coord = {(Fp(x.evaluate(pl)), Fp(w.evaluate(pl))): pl for pl in finite}
    def lift(P):
        if P.is_zero(): return None
        xP, yP = Fp(P[0]), Fp(P[1])
        if not yP.is_square(): return None
        r = yP.sqrt()
        if Integer(r) > (p - 1) // 2: r = -r
        a = coord.get((xP, r)); b = coord.get((xP, -r))
        return None if (a is None or b is None) else G0.point(a.divisor() - b.divisor())
    phi = lambda P: E(beta * P[0], P[1]); phi2 = lambda P: E(b2 * P[0], P[1])
    def build_S(P):
        Q0, Q1, Q2 = lift(P), lift(phi(P)), lift(phi2(P))
        if None in (Q0, Q1, Q2): return None
        return Q0 + Integer(b2) * Q1 + Integer(beta) * Q2
    n = E.order()
    M = p^2 + p + 1
    rat = [d for d in range(1, n) if Fp((d * Gp)[1]).is_square()]
    SAMPLE = rat if len(rat) <= 80 else rat[:40] + rat[-40:]
    orders = {}
    for d in SAMPLE:
        S = build_S(d * Gp)
        if S is None: continue
        orders[int(d)] = int(S.order())
    from sage.all import factor as sfactor
    Mf = [[int(q), int(e)] for (q, e) in sfactor(M)]
    out[int(p)] = {"n": int(n), "M": int(M), "M_factor": Mf, "orders": orders}
    json.dump(out, open("/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/anew_sorder_sweep_v2.json", "w"))
    print(f"p={p}: n={n} M={M}={Mf} | S-orders multiset {sorted(set(orders.values()))} "
          f"[{time.time()-t0:.0f}s]", flush=True)
json.dump(out, open("/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/anew_sorder_sweep.json", "w"))
print("dumped anew_sorder_sweep.json", flush=True)
