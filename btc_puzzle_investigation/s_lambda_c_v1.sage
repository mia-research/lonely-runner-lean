#!/usr/bin/env sage
# s_lambda_c_v1 — close SB-owed: measure c INDEPENDENTLY, then predict blindness.
#
# Testing BOTH primitive cube roots over-predicts blindness at (79,ell=7) and (163,ell=7),
# where ground truth is SEEN. Under the scalar-lambda model the true c must be the other root.
# c is defined by the phi-ACTION: lift(phi P) = c * lift(P) in A_new(F_p) = Z/M.
# Measuring c from the action and THEN predicting lambda is non-circular (S is never used).
#
# PREDICTION: with the measured c, lambda = 1 + b2*c + beta*c^2 has gcd(lambda, M) = 1
#             at p=79 and p=163 (both fully visible in the sweep).
# FALSIFIER: gcd(lambda, M) = 7 at either prime.
import sys, time
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import os
p = Integer(os.environ["PP"]); B = 7
Fp = GF(p)
K.<x> = FunctionField(Fp); R.<T> = K[]
L.<w> = K.extension(T**4 - (x**3 + B))
J = L.jacobian(model='hess'); G0 = J.group()
E = EllipticCurve(Fp, [0, B]); Gp = E.gens()[0]
n = E.order(); M = p**2 + p + 1
beta = next(c for c in range(2, p) if pow(c, 3, p) == 1 and c != 1); b2 = beta**2 % p
print(f"p={p} n={n} M={M}={factor(M)} beta={beta} b2={b2}", flush=True)
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
phi = lambda P: E(beta * P[0], P[1])
t0 = time.time()  # noqa: float — (display) elapsed-time logging only, never fed back into any decision
found = []
for d in range(1, n):
    P = d * Gp
    if not Fp(P[1]).is_square(): continue
    D, D3 = lift(P), lift(phi(P))
    if D is None or D3 is None: continue
    o = Integer(D.order())
    if o < 3: continue
    # c^3 = 1 mod o, so only the cube roots of unity mod o are candidates -- test each
    # against the ACTION (D3 == c*D). No discrete log needed.
    cands = [k for k in range(o) if pow(k, 3, o) == 1]
    c = next((Integer(k) for k in cands if Integer(k) * D == D3), None)
    if c is None:
        print(f"  d={d}: ord={o}: no cube root of 1 mod ord reproduces the action "
              f"({len(cands)} candidates) -- lift NOT phi-equivariant here", flush=True)
        continue
    ok = (c**3 - 1) % o == 0
    lam = (1 + b2*c + beta*c*c) % o
    g = gcd(Integer(lam), o)
    found.append((d, o, c, lam, g))
    print(f"  d={d}: ord(D)={o} (M/{M//o})  c={c}  c^3=1 mod ord ? {ok}  "
          f"lambda={lam}  gcd(lambda,ord)={g}  -> {'BLIND to '+str(factor(g)) if g>1 else 'sees everything in <D>'}"
          f"  [{time.time()-t0:.0f}s]", flush=True)  # noqa: float — (display) elapsed-time logging only, never fed back into any decision
    if len(found) >= 4: break
