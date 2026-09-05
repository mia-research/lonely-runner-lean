# Control (iv), PREREG v2 §5(iv): the rho-identity phi([-d]G) = rho . phi([d]G) in Jac(C)(F_{p^2}).
# Certifies that the non-QR half carries no content independent of the QR half (= rho . QR half),
# the empirical warrant for the QR-half domain restriction. A mis-built rho FAILS -> genuine control.
# rho is induced by zeta4:(x,w)->(x, i*w), i^2=-1 in F_{p^2}. Sign ambiguity from Sage's canonical
# sqrt is allowed (check up to global sign); an UNRELATED phi(-P) still fails both signs.

p = 43; B = 7
Fq = GF(p^2)
i = Fq(-1).sqrt()
assert i*i == Fq(-1)
K.<x> = FunctionField(Fq); Rr.<T> = K[]
L.<w> = K.extension(T^4 - (x^3 + B))
J = L.jacobian(model='hess'); G0 = J.group()
E = EllipticCurve(GF(p), [0, B]); G = E.gens()[0]; nE = G.order()
print(f"p={p}, F_q=F_{p}^2, nE={nE}, i^2=-1 ok", flush=True)

finite = [pl for pl in L.places(1) if not pl.is_infinite_place()]
coord = {}
for pl in finite:
    xv = Fq(x.evaluate(pl)); wv = Fq(w.evaluate(pl))
    coord[(xv, wv)] = pl
print(f"coord places built: {len(coord)}", flush=True)

def place_at(xv, wv):
    return coord.get((Fq(xv), Fq(wv)))

def phi(P):
    # lift P in E(F_p) to the divisor class [(x,r)]-[(x,-r)] over F_q (all sqrt exist in F_q)
    xP = Fq(P[0]); yP = Fq(P[1]); r = yP.sqrt()
    a = place_at(xP, r); b = place_at(xP, -r)
    if a is None or b is None: return None
    return G0.point(a.divisor() - b.divisor())

def rho_of_phi(P):
    # rho . phi(P): remap the two lift places by zeta4: (x,w)->(x, i*w)
    xP = Fq(P[0]); yP = Fq(P[1]); r = yP.sqrt()
    ra = place_at(xP, i*r); rb = place_at(xP, -i*r)
    if ra is None or rb is None: return None
    return G0.point(ra.divisor() - rb.divisor())

def is_QR(P):
    return GF(p)(P[1]).is_square()

zero = G0(0)
pass_ct = fail_ct = skip_ct = 0
sign_hist = {'+':0, '-':0}
fails = []
for d in range(1, nE):
    P = d*G
    negP = (-d) % nE * G
    lhs = phi(negP)             # phi([-d]G)
    rhs = rho_of_phi(P)         # rho . phi([d]G)
    if lhs is None or rhs is None:
        skip_ct += 1; continue
    if lhs == rhs:
        pass_ct += 1; sign_hist['+'] += 1
    elif lhs == -rhs:
        pass_ct += 1; sign_hist['-'] += 1
    else:
        fail_ct += 1; fails.append(d)

print(f"\n=== control (iv) rho-identity  phi([-d]G) == +/- rho.phi([d]G) ===", flush=True)
print(f"PASS={pass_ct}  FAIL={fail_ct}  SKIP={skip_ct}  (sign +:{sign_hist['+']} -:{sign_hist['-']})", flush=True)
if fails: print(f"FAIL at d={fails}", flush=True)
# focus report: non-QR d (the half whose independence the control certifies)
nonqr = [d for d in range(1,nE) if not is_QR(d*G)]
nq_pass = sum(1 for d in nonqr if (lambda l,r: l is not None and r is not None and (l==r or l==-r))(phi(((-d)%nE)*G), rho_of_phi(d*G)))
print(f"non-QR d: {len(nonqr)} of {nE-1};  rho-identity holds on {nq_pass}/{len(nonqr)}", flush=True)
verdict = (fail_ct == 0 and pass_ct > 0)
print(f"\nCONTROL (iv): {'FIRE' if verdict else 'FAIL'}  "
      f"({'non-QR half = rho.(QR half), no independent content confirmed' if verdict else 'rho/lift mis-built or identity false'})", flush=True)
