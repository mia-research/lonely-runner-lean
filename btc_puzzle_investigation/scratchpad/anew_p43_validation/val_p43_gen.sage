# PRE-REG PREREG_anew_direct_invariant_partialinfo_v1 — p=43 VALIDATION data generation (R3, Sage).
# Purpose: produce exact-integer per-d data so the int-only stats harness can confirm the
#   pipeline runs and the THREE CONTROLS fire. NOT a verdict run (underpowered by construction).
# Reuses the established S([d]G) construction (scratchpad/session_2026-08-11/trace_openq_test.sage):
#   S = isotypic projection of the ODD (difference) 4th-root preimage on C: w^4=x^3+B.
#   S_closed = same isotypic combo of the EVEN (sum) preimage -> factors through Hom(E,A_new)=0
#              -> A_new-projection forced trivial -> d-INDEPENDENT (the matched control).
import json
p = 43; B = 7
Fp = GF(p)
K.<x> = FunctionField(Fp); Rr.<T> = K[]
L.<w> = K.extension(T^4 - (x^3 + B))
J = L.jacobian(model='hess'); G0 = J.group()
E = EllipticCurve(Fp, [0, B]); G = E.gens()[0]; nE = Integer(G.order())
beta = Fp(36); b2 = beta^2
# GLV multiplier lambda on E: phi(P) = [lam]P
lam = None
for cand in range(2, nE):
    if E(beta*G[0], G[1]) == cand*G: lam = Integer(cand); break
finite = [pl for pl in L.places(1) if not pl.is_infinite_place()]
coord = {(Fp(x.evaluate(pl)), Fp(w.evaluate(pl))): pl for pl in finite}
_c = {}
def places_over(P):
    # returns (a,b) = places over (x, +r),(x, -r), r=sqrt(y); or (None,None)
    if P.is_zero(): return (None, None)
    xP, yP = Fp(P[0]), Fp(P[1])
    if not yP.is_square(): return (None, None)
    r = yP.sqrt()
    return (coord.get((xP, r)), coord.get((xP, -r)))
def lift_odd(P):        # S : difference (non-Galois-closed, odd under w->-w)
    a, b = places_over(P)
    if a is None or b is None: return None
    return G0.point(a.divisor() - b.divisor())
BASE_FIBER = None       # set once below (degree-2 divisor of a fixed base point's fiber)
def lift_even(P):       # S_closed : (fiber(P) - fiber(base)) = pullback of [P]-[base] -> E-part only, deg 0
    a, b = places_over(P)
    if a is None or b is None: return None
    return G0.point(a.divisor() + b.divisor() - BASE_FIBER)
phi  = lambda P: E(beta*P[0], P[1]);  phi2 = lambda P: E(b2*P[0], P[1])
def build(P, lift):
    Q0, Q1, Q2 = lift(P), lift(phi(P)), lift(phi2(P))
    if None in (Q0, Q1, Q2): return None
    return Q0 + Integer(b2)*Q1 + Integer(beta)*Q2
build_S        = lambda P: build(P, lift_odd)
build_S_closed = lambda P: build(P, lift_even)

# ---- A_new order, dlog table (for N14 reproduction only), and the DLP-FREE f5 machinery ----
rat = [d for d in range(1, nE) if Fp((d*G)[1]).is_square()]
cands = [build_S(d*G) for d in rat]
cands = [S for S in cands if S is not None and Integer(S.order()) == 1893]
base = cands[0]; zero = base - base
# fixed base fiber for the (degree-0) matched control S_closed
_ab0, _bb0 = places_over(rat[0] * G)
BASE_FIBER = _ab0.divisor() + _bb0.divisor()
ANEW = 1893; l0 = 3; cof = ANEW // l0            # 631
tab = {}; cur = zero
for i in range(ANEW): tab[str(cur)] = i; cur = cur + base
def dlog(S): return tab.get(str(S), None)
# 3-torsion basis for the DLP-free label: {0, [cof]base, [2cof]base}
tor3 = {str(Integer(j*cof) * base): j for j in range(l0)}
def anew_part(X):        # kill E-part by [nE]; leaves the order-1893 A_new component
    return Integer(nE) * X
def f5_label(X):         # DLP-FREE: point-mult only, then size-3 lookup. None if off A_new[3].
    Y = Integer(cof) * anew_part(X)
    return tor3.get(str(Y), None)

# ---- per-d records ----
records = []
for d in range(1, nE):
    P = d*G
    Sd = build_S(P); Scd = build_S_closed(P)
    ell = dlog(Sd) if Sd is not None else None
    rec = {
        "d": int(d),
        "has_lift": bool(Sd is not None),
        "ell": (int(ell) if ell is not None else None),          # N14 diagnostic only (uses dlog)
        "f5_open":   (None if Sd  is None else (int(f5_label(Sd))  if f5_label(Sd)  is not None else -1)),
        "f5_closed": (None if Scd is None else (int(f5_label(Scd)) if f5_label(Scd) is not None else -1)),
        "Sclosed_str": (None if Scd is None else str(anew_part(Scd))),   # for distinctness check
    }
    records.append(rec)

# ---- N14 reproduction (covariance k, affine, homomorphism) ----
ell = {r["d"]: r["ell"] for r in records}
ks = set()
for d in range(1, nE):
    ld = (lam*d) % nE
    if ell.get(d) and ell.get(ld):
        e, el = ell[d], ell[ld]; g = gcd(e, ANEW)
        if el % g == 0:
            ks.add(int((el//g) * inverse_mod(e//g, ANEW//g) % (ANEW//g)))
pts = [(d, ell[d]) for d in range(1, nE) if ell.get(d) is not None]
aff_viol = aff_tot = None
if len(pts) >= 3:
    (da, ea), (db, eb) = pts[0], pts[1]
    try:
        a = ((eb-ea) * inverse_mod((db-da) % ANEW, ANEW)) % ANEW; bb = (ea - a*da) % ANEW
        aff_viol = int(sum(1 for (d, e) in pts if (a*d+bb) % ANEW != e)); aff_tot = int(len(pts))
    except Exception: pass
hpairs = [(d, ell[d], ell.get((2*d) % nE)) for d in range(1, nE//2) if ell.get(d) and ell.get((2*d) % nE)]
hom_ok = int(sum(1 for d, e, e2 in hpairs if (2*e) % ANEW == e2)); hom_tot = int(len(hpairs))

out = {
    "p": int(p), "B": int(B), "nE": int(nE), "lam": int(lam),
    "anew_order": int(ANEW), "l0": int(l0), "cof": int(cof),
    "n_rational_lifts": int(len(pts)),
    "records": records,
    "n14": {"k_multipliers": sorted(ks), "k_expected_psq_mod_anew": int((p*p) % ANEW),
            "affine_violations": aff_viol, "affine_total": aff_tot,
            "hom_holds": hom_ok, "hom_total": hom_tot},
}
with open("val_p43_data.json", "w") as fh: json.dump(out, fh, indent=1)
print("WROTE val_p43_data.json  nE=%d lam=%d anew=%d rational_lifts=%d" % (nE, lam, ANEW, len(pts)))
print("N14: k=%s (expect p^2 mod anew=%d) | affine %s/%s | hom %d/%d"
      % (sorted(ks), (p*p) % ANEW, aff_viol, aff_tot, hom_ok, hom_tot))
distinct_closed = len(set(r["Sclosed_str"] for r in records if r["Sclosed_str"] is not None))
print("matched-control premise: distinct S_closed A_new-parts = %d (1 => d-independent)" % distinct_closed)
