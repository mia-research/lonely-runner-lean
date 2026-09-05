#!/usr/bin/env sage
# brick_e_rung_v2.sage — powered Brick E rung, per PREREG_brick_e_cd_degree_v2.md (frozen).
# v2 fixes over v1 (DEVIATIONS D5, D6):
#   D5 — WELL-POSEDNESS: the degree fit needs a prime factor q | |A_new(F_p)|=p^2+p+1 with q >= n,
#        else the domain d in [1,n) collides mod q and no CRT factor is fittable (v1's chosen powered
#        rungs 67/79/163/211 all fail: qmax < n). This runner ASSERTS qmax >= n and works in the
#        order-qmax subgroup (Pohlig-Hellman), so cptab is c+(d) mod qmax directly (M := qmax, prime).
#   D6 — control-iv I2: v1 used Fq.gen() which is a root of the DEFAULT modulus, not sqrt(-1);
#        fixed to I2 = Fq(-1).sqrt() (valid for p=3 mod4).
# Usage: sage brick_e_rung_v2.sage <p>   (well-posed rungs: 43, 127, 547, 907, 967, ...).
# Output: brick_e_rung_<p>_v2_data.json (c+ mod qmax + metadata + control iv).
import sys, json, time
sys.path.insert(0, "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
import audit_n1_vsign_v2_core as core

import hashlib
H = hashlib.sha256(open("/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/PREREG_brick_e_cd_degree_v2.md","rb").read()).hexdigest()
EXPECTED = "e3fe35d0e5d847f5ea5a51c2bbb290ab85b001436d4732a83f7123e01f4eb2f3"
print(f"[freeze] PREREG sha256 = {H}  match = {H == EXPECTED}", flush=True)
assert H == EXPECTED, "PREREG NOT FROZEN AS EXPECTED — ABORT"

p = Integer(sys.argv[1]); B = 7
assert p % 12 == 7, "rung must be p = 7 mod 12"
Fp = GF(p)
K.<x> = FunctionField(Fp); R.<T> = K[]
L.<w> = K.extension(T^4 - (x^3 + B))
J = L.jacobian(model='hess'); G0 = J.group()
E = EllipticCurve(Fp, [0, B])
n = core.curve_order(p)
assert is_prime(n) and (n - 1) % 6 == 0, f"rung inadmissible: n={n}"
M = p^2 + p + 1
qmax = int(max(q for q, e in factor(M)))
assert qmax >= n, f"rung NOT well-posed: qmax={qmax} < n={n} (degree fit ill-posed, D5)"
Gp = None
for xx in range(1, p):
    rr = (xx**3 + B) % p
    if pow(rr, (p - 1) // 2, p) != 1: continue
    yy = core.tonelli(rr, p)
    if yy is not None and (yy * yy) % p == rr:
        Gp = E(xx, yy); break
if Gp is None or Gp.order() != n: Gp = E.gens()[0]
assert Gp.order() == n
print(f"[rung] p={p} n={n} |A_new|={M}={factor(M)}  qmax={qmax} (>= n, WELL-POSED)", flush=True)

beta = None
for c in range(2, p):
    if pow(c, 3, p) == 1 and c != 1: beta = c; break
b2 = beta^2 % p
phi = lambda P: E(beta * P[0], P[1])
lam = None
for l in range(1, n):
    if (l * Gp) == phi(Gp): lam = l; break
assert lam is not None and pow(lam, 3, n) == 1 and lam != 1
print(f"[glv] beta={beta} lambda={lam}", flush=True)

t0 = time.time()
finite = [pl for pl in L.places(1) if not pl.is_infinite_place()]
coord = {(Fp(x.evaluate(pl)), Fp(w.evaluate(pl))): pl for pl in finite}
print(f"[instrument] {len(finite)} degree-1 places [{time.time()-t0:.0f}s]", flush=True)
_c = {}
def lift(P):
    if P.is_zero(): return None
    k = (P[0], P[1])
    if k in _c: return _c[k]
    xP, yP = Fp(P[0]), Fp(P[1])
    if not yP.is_square(): _c[k] = None; return None
    r = yP.sqrt()
    if Integer(r) > (p - 1) // 2: r = -r
    a = coord.get((xP, r)); b = coord.get((xP, -r))
    _c[k] = None if (a is None or b is None) else G0.point(a.divisor() - b.divisor())
    return _c[k]
phi2 = lambda P: E(b2 * P[0], P[1])
def build_S(P):
    Q0, Q1, Q2 = lift(P), lift(phi(P)), lift(phi2(P))
    if None in (Q0, Q1, Q2): return None, None
    return Q0 + Integer(b2) * Q1 + Integer(beta) * Q2, Q1 + Integer(b2) * Q2 + Integer(beta) * Q0

rat = [d for d in range(1, n) if Fp((d * Gp)[1]).is_square()]
print(f"[domain] QR half |Q| = {len(rat)} of {n-1} [{time.time()-t0:.0f}s]", flush=True)
cands = [build_S(d * Gp)[0] for d in rat]
cands = [S for S in cands if S is not None]
# Pohlig-Hellman: M=p^2+p+1 is squarefree (=> A_new(F_p) cyclic); project to the Sylow-qmax
# subgroup via the GROUP cofactor M//qmax. Avoids per-element .order() (D5b: the p=547 hang).
cof = M // qmax
zero = cands[0] - cands[0]
base = None
for S in cands:
    cb = cof * S
    if cb != zero: base = cb; break
assert base is not None, "no candidate has a nontrivial qmax-part"
tab = {}; cur = zero
for i in range(qmax):
    tab[str(cur)] = i; cur = cur + base
assert len(tab) == qmax, f"Sylow-{qmax} not faithful: {len(tab)} != {qmax}"
print(f"[dlog] qmax={qmax}-subgroup table built [{time.time()-t0:.0f}s]", flush=True)
def dlogq(S):
    return tab.get(str(cof * S), None)

cptab = {}; dropped = 0
for d in rat:
    S, sS = build_S(d * Gp)
    e = dlogq(S) if S is not None else None
    if e is None: dropped += 1; continue
    cptab[d] = e
# covariance mod qmax
ratios = set()
for d in rat:
    d2 = (lam * d) % n
    if d in cptab and d2 in cptab and gcd(cptab[d], qmax) == 1:
        ratios.add(cptab[d2] * inverse_mod(cptab[d], qmax) % qmax)
kk = next(iter(ratios)) if len(ratios) == 1 else None
print(f"[covariance] kappa_eff (mod qmax): {sorted(ratios)} global={kk is not None}"
      + (f" k^3%qmax={pow(kk,3,qmax)} k!=1:{kk!=1}" if kk is not None else ""), flush=True)

out = {"p": int(p), "n": int(n), "M": int(qmax), "M_full": int(M),
       "M_factor": [[int(qmax), 1]], "qmax": int(qmax), "ph_subgroup": True,
       "beta": int(beta), "lam": int(lam), "kappa": int(kk) if kk is not None else None,
       "kappa_global": kk is not None, "mu3_covariance_ok": kk is not None,
       "cplus": {int(d): int(cptab[d]) for d in cptab}, "dropped_outside_base": int(dropped),
       "control_iv": {"ok": None, "cnt": 0, "fails": [], "note": "not yet run at dump time"}}
fn = f"/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/brick_e_rung_{p}_v2_data.json"
json.dump(out, open(fn, "w"), default=int)
print(f"[dump-early] {fn} (dropped {dropped})", flush=True)

# ---- control (iv): rho-identity in F_{p^2} (D6 fix: I2 = sqrt(-1), not Fq.gen()) ----
Fq = GF(p^2, 'i2')
I2 = Fq(-1).sqrt()
assert I2^2 == -1
Kq.<xq> = FunctionField(Fq); Rq.<Tq> = Kq[]
Lq.<wq> = Kq.extension(Tq^4 - (xq^3 + B))
Jq = Lq.jacobian(model='hess'); G0q = Jq.group()
finiteq = [pl for pl in Lq.places(1) if not pl.is_infinite_place()]
coordq = {(Fq(xq.evaluate(pl)), Fq(wq.evaluate(pl))): pl for pl in finiteq}
def liftq_fp(Pj):
    xP = Fq(Fp(Pj[0])); yP = Fq(Fp(Pj[1])); r = yP.sqrt()
    for rr in (r, -r):
        a = coordq.get((xP, rr)); b = coordq.get((xP, -rr))
        if a is not None and b is not None: return a, b
    return None, None
def rho_place(pl):
    x0 = Fp(xq.evaluate(pl)); w0 = Fq(wq.evaluate(pl))
    return coordq.get((Fq(x0), I2 * w0))
t0iv = time.time(); iv_ok = 0; iv_cnt = 0; iv_fail = []
for d in range(1, n):
    P = d * Gp
    if Fp(P[1]).is_square(): continue
    iv_cnt += 1; negP = -P
    try:
        Qa = G0q.point(liftq_fp(P)[0].divisor() - liftq_fp(P)[1].divisor()) if None not in liftq_fp(P) else None
        la, lb = liftq_fp(negP); ma, mb = liftq_fp(phi(negP)); na, nb = liftq_fp(phi2(negP))
        pa, pb = liftq_fp(P); qa, qb = liftq_fp(phi(P)); ra, rb = liftq_fp(phi2(P))
        if None in (la, ma, na, pa, qa, ra):
            iv_fail.append((d, "qr-lift-missing")); continue
        rhoS = (G0q.point(rho_place(la).divisor() - rho_place(lb).divisor())
                + Integer(b2) * G0q.point(rho_place(ma).divisor() - rho_place(mb).divisor())
                + Integer(beta) * G0q.point(rho_place(na).divisor() - rho_place(nb).divisor()))
        Sd = (G0q.point(pa.divisor() - pb.divisor())
              + Integer(b2) * G0q.point(qa.divisor() - qb.divisor())
              + Integer(beta) * G0q.point(ra.divisor() - rb.divisor()))
        if Sd == rhoS or Sd == -rhoS: iv_ok += 1
        else: iv_fail.append((d, "identity-fails"))
    except Exception as ex:
        iv_fail.append((d, f"err:{ex}"))
print(f"[control iv] rho-identity: {iv_ok}/{iv_cnt} non-QR d (fails {iv_fail[:5]}) [{time.time()-t0iv:.0f}s]", flush=True)
out["control_iv"] = {"ok": int(iv_ok), "cnt": int(iv_cnt), "fails": [[int(a), str(b)] for (a, b) in iv_fail[:20]]}
json.dump(out, open(fn, "w"), default=int)
print(f"[dump-final] {fn} (control iv {iv_ok}/{iv_cnt})", flush=True)
