#!/usr/bin/env sage
# brick_e_control_iv_v1.sage — standalone control (iv): the rho-identity in F_{p^2}.
# For each non-QR d: S_{F_{p^2}}([d]G)  ==  rho . S([−d]G)  (up to sign, branch-documented).
# Runs WITHOUT the dlog table (cheap). Usage: sage brick_e_control_iv_v1.sage <p>
import sys
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import audit_n1_vsign_v2_core as core

p = Integer(sys.argv[1]); B = 7
Fp = GF(p)
K.<x> = FunctionField(Fp); R.<T> = K[]
L.<w> = K.extension(T^4 - (x^3 + B))
J = L.jacobian(model='hess'); G0 = J.group()
E = EllipticCurve(Fp, [0, B])
n = core.curve_order(p)
Gp = E.gens()[0]
beta = None
for c in range(2, p):
    if pow(c, 3, p) == 1 and c != 1:
        beta = c; break
b2 = beta^2 % p
phi = lambda P: E(beta * P[0], P[1]); phi2 = lambda P: E(b2 * P[0], P[1])
print(f"[iv] p={p} n={n} beta={beta}", flush=True)

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

Rmod = PolynomialRing(Fp, 'z')
zgen = Rmod.gen()
Fq = GF(p^2, 'i2', modulus=Rmod(zgen^2 + 1))
I2 = Fq.gen()
assert I2^2 == -1
Kq.<xq> = FunctionField(Fq); Rq.<Tq> = Kq[]
Lq.<wq> = Kq.extension(Tq^4 - (xq^3 + B))
Jq = Lq.jacobian(model='hess'); G0q = Jq.group()
finiteq = [pl for pl in Lq.places(1) if not pl.is_infinite_place()]
coordq = {(Fq(xq.evaluate(pl)), Fq(wq.evaluate(pl))): pl for pl in finiteq}
print(f"[iv] F_p^2 places: {len(finiteq)}", flush=True)

def liftq_fp(Pj):
    xP = Fq(Fp(Pj[0])); yP = Fq(Fp(Pj[1]))
    r = yP.sqrt()
    for rr in (r, -r):
        a = coordq.get((xP, rr)); b = coordq.get((xP, -rr))
        if a is not None and b is not None:
            return a, b
    return None, None
def liftq_full(P):
    # lift a NON-QR point: sqrt lands in F_{p^2}
    xP = Fq(Fp(P[0])); yP = Fq(Fp(P[1]))
    r = yP.sqrt()
    for rr in (r, -r):
        a = coordq.get((xP, rr)); b = coordq.get((xP, -rr))
        if a is not None and b is not None:
            return G0q.point(a.divisor() - b.divisor())
    return None
def rho_place(pl):
    x0 = Fp(xq.evaluate(pl)); w0 = Fq(wq.evaluate(pl))
    return coordq.get((Fq(x0), I2 * w0))

ok = 0; cnt = 0; fails = []
for d in range(1, n):
    P = d * Gp
    if Fp(P[1]).is_square():
        continue
    cnt += 1
    negP = -P
    try:
        Qa = liftq_full(P); Qb = liftq_full(phi(P)); Qc = liftq_full(phi2(P))
        la, lb = liftq_fp(negP); ma, mb = liftq_fp(phi(negP)); na, nb = liftq_fp(phi2(negP))
        if None in (Qa, Qb, Qc) or la is None or ma is None or na is None:
            fails.append((int(d), "lift-missing")); continue
        rhoS = (G0q.point(rho_place(la).divisor() - rho_place(lb).divisor())
                + Integer(b2) * G0q.point(rho_place(ma).divisor() - rho_place(mb).divisor())
                + Integer(beta) * G0q.point(rho_place(na).divisor() - rho_place(nb).divisor()))
        Sd = Qa + Integer(b2) * Qb + Integer(beta) * Qc
        if Sd == rhoS or Sd == -rhoS:
            ok += 1
        else:
            fails.append((int(d), "identity-fails"))
    except Exception as ex:
        fails.append((int(d), f"err:{type(ex).__name__}"))
print(f"[control iv] rho-identity: {ok}/{cnt} non-QR d  (fails: {fails[:10]})", flush=True)
