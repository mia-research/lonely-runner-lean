#!/usr/bin/env sage
# s_beta_swap_v1 — is S-visibility a fact about A_new, or about the choice of beta?
#
# S = Q0 + b2*Q1 + beta*Q2 with Q_i = lift(phi^i P), phi = (x -> beta*x).
# If lift is phi-equivariant this is 3 x (projector onto the phi = omega eigenplane).
# The sweep picks beta = FIRST c>1 with c^3=1 mod p — an arbitrary pick between the two
# primitive cube roots.  Swapping beta <-> beta^2 projects onto the OTHER eigenplane.
#
# The pi=1 line mod ell is 1-dimensional and lies in exactly ONE of the two planes.
# PREDICTION if the eigenplane picture is right: under beta-swap the visible set and the
# blind set EXCHANGE.  At p=211 (M = 3*13*31*37, S sees 31,37 blind to 13) the swapped S
# should see 13 and go blind to 31,37.
# FALSIFIER: if both betas give the same visibility, S-visibility is beta-independent and
# the eigenplane story is wrong (or lift is not phi-equivariant).
import sys, time
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")

p = 211; B = 7
Fp = GF(p)
K.<x> = FunctionField(Fp); R.<T> = K[]
L.<w> = K.extension(T**4 - (x**3 + B))
J = L.jacobian(model='hess'); G0 = J.group()
E = EllipticCurve(Fp, [0, B]); Gp = E.gens()[0]
n = E.order(); M = p**2 + p + 1
betas = [c for c in range(2, p) if pow(c, 3, p) == 1 and c != 1]
print(f"p={p} n={n} M={M}={factor(M)} | primitive cube roots mod p: {betas}", flush=True)

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

rat = [d for d in range(1, n) if Fp((d * Gp)[1]).is_square()]
SAMPLE = rat[:14]
for beta in betas:
    t0 = time.time()  # noqa: float — (display) elapsed-time logging only, never fed back into any decision
    b2 = beta**2 % p
    phi = lambda P: E(beta * P[0], P[1]); phi2 = lambda P: E(b2 * P[0], P[1])
    orders = []
    for d in SAMPLE:
        P = d * Gp
        Q0, Q1, Q2 = lift(P), lift(phi(P)), lift(phi2(P))
        if None in (Q0, Q1, Q2): continue
        S = Q0 + Integer(b2) * Q1 + Integer(beta) * Q2
        orders.append(Integer(S.order()))
    sub = lcm(orders) if orders else 0
    seen = [q for q, e in factor(M) if sub % q == 0]
    blind = [q for q, e in factor(M) if sub % q != 0]
    print(f"  beta={beta:4d} (b2={b2:4d}): {len(orders)} pts, orders {sorted(set(orders))}", flush=True)
    print(f"      subgroup order lcm = {sub} = M/{M//sub if sub else 0} | SEES {seen} | BLIND to {blind}  [{time.time()-t0:.0f}s]", flush=True)  # noqa: float — (display) elapsed-time logging only, never fed back into any decision
