# R1 POWERED generator (generalized): S([d]G) in A_new(F_p) via Sage genus-3 Jac GROUP LAW at scale.
# No dlog table, no .order() (the two things that hung). |A_new| determined empirically (min candidate
# order annihilating A_new elements); f5 = ell0-torsion label, ell0 = smallest prime | |A_new| (DLP-free:
# scalar-mult + finite lookup). Matched control S_closed (even lift). Emits exact-int data for val_stats.py.
# Usage: sage powered_gen.sage <p>   (p == 7 mod 12; scans twists for a prime-order, 3|nE-1 curve).
import sys, json, time
p = int(sys.argv[1]) if len(sys.argv) > 1 else 691
assert p % 12 == 7, "need p == 7 mod 12"
Fp = GF(p); Kf.<x> = FunctionField(Fp); Rr.<T> = Kf[]
beta = next(c for c in Fp if c != 1 and c^3 == 1); b2 = beta^2
t0 = time.time()

def build_curve(B):
    E = EllipticCurve(Fp, [0, B]); nE = Integer(E.order())
    if not nE.is_prime() or (nE - 1) % 3 != 0: return None
    G = E.gens()[0]
    lam = None
    for cand in range(2, nE):
        if E(beta*G[0], G[1]) == cand*G: lam = Integer(cand); break
    if lam is None or (lam^3) % nE != 1 or lam % nE == 1: return None
    L = Kf.extension(T^4 - (x^3 + B)); G0 = L.jacobian(model='hess').group(); wv = L.gen()
    finite = [pl for pl in L.places(1) if not pl.is_infinite_place()]
    coord = {(Fp(x.evaluate(pl)), Fp(wv.evaluate(pl))): pl for pl in finite}
    def places_over(P):
        if P.is_zero(): return (None, None)
        xP, yP = Fp(P[0]), Fp(P[1])
        if not yP.is_square(): return (None, None)
        r = yP.sqrt(); return (coord.get((xP, r)), coord.get((xP, -r)))
    d_first = next(d for d in range(1, nE) if Fp((d*G)[1]).is_square())
    a0, b0 = places_over(d_first * G)
    if a0 is None or b0 is None: return None
    BASE = a0.divisor() + b0.divisor()
    def lift_odd(P):
        a, b = places_over(P)
        return None if (a is None or b is None) else G0.point(a.divisor() - b.divisor())
    def lift_even(P):
        a, b = places_over(P)
        return None if (a is None or b is None) else G0.point(a.divisor() + b.divisor() - BASE)
    phi = lambda P: E(beta*P[0], P[1]); phi2 = lambda P: E(b2*P[0], P[1])
    def build(P, lift):
        Q0, Q1, Q2 = lift(P), lift(phi(P)), lift(phi2(P))
        if None in (Q0, Q1, Q2): return None
        return Q0 + Integer(b2)*Q1 + Integer(beta)*Q2
    anew_part = lambda X: Integer(nE) * X       # kill E-part (order | nE) -> pure A_new element
    return dict(E=E, nE=nE, G=G, lam=lam, bS=lambda P: build(P, lift_odd),
                bSc=lambda P: build(P, lift_even), anew_part=anew_part)

CTX = None; Bsel = None
for B in range(1, 600):
    CTX = build_curve(B)
    if CTX: Bsel = B; break
assert CTX is not None, "no prime-order (3|nE-1) curve found in B range for p=%d" % p
E = CTX['E']; nE = CTX['nE']; G = CTX['G']; lam = CTX['lam']
build_S = CTX['bS']; build_S_closed = CTX['bSc']; anew_part = CTX['anew_part']

# --- determine |A_new| empirically: min candidate supersingular order annihilating 3 A_new elements ---
rat = [d for d in range(1, nE) if Fp((d*G)[1]).is_square()]
Qsamp = []
for d in rat:
    S = build_S(d*G)
    if S is not None:
        Q = anew_part(S)
        if not Q.is_zero(): Qsamp.append(Q)
    if len(Qsamp) >= 3: break
cands = sorted({p*p+p+1, p*p-p+1, p*p+1, (p+1)*(p+1), (p-1)*(p-1), p*p-1, (p+1)*(p-1)})
ANEW = None
for O in cands:
    if all((Integer(O) * Q).is_zero() for Q in Qsamp): ANEW = Integer(O); break
assert ANEW is not None, "no candidate order annihilates A_new sample (p=%d B=%d)" % (p, Bsel)
small_ells = [q for q in Integer(ANEW).prime_factors() if q <= 97]   # 3 and each ell>3 up to L_MAX
l0 = small_ells[0]; cof = ANEW // l0
# per-ell lazy torsion-label tables (DLP-free: [ANEW/ell]*anew_part lands in A_new[ell])
_idst = {q: {} for q in small_ells}
def flabel(X, q):
    ids = _idst[q]; Y = Integer(ANEW // q) * anew_part(X); s = str(Y)
    if s not in ids: ids[s] = len(ids)
    return ids[s]
def f5(X): return flabel(X, l0)                 # ell0=3 (parent invariant, kept)

# --- orbit-dedup: one canonical rep (min of {d,lam d,lam^2 d}) per liftable orbit ---
seen = set(); records = []; nlift = 0
for d in range(1, nE):
    orb = tuple(sorted((int(d % nE), int((lam*d) % nE), int((lam*lam*d) % nE))))
    if orb in seen: continue
    seen.add(orb)
    cano = orb[0]
    P = cano * G
    if cano == 0 or not Fp(P[1]).is_square(): continue
    Sd = build_S(P); Scd = build_S_closed(P)
    if Sd is None: continue
    nlift += 1
    # f6 (frozen menu): parity + sextant of the C-lift w-coordinate w = sqrt(y).  DLP-free; a MARGINAL
    # readout of [d]G's y (no A_new projection), so it has no S_closed matched control.
    wc = Integer(Fp(P[1]).sqrt())
    f6 = int((wc % 2) * 6 + (6 * wc) // p)      # alphabet 0..11
    records.append({
        "d": int(cano), "has_lift": True, "ell": None,
        "f5_open": int(f5(Sd)),
        "f5_closed": (None if Scd is None else int(f5(Scd))),
        "f6_open": f6,
        "fell_open": {str(q): int(flabel(Sd, q)) for q in small_ells if q > 3},
        "fell_closed": (None if Scd is None else {str(q): int(flabel(Scd, q)) for q in small_ells if q > 3}),
        "Sclosed_str": (None if Scd is None else str(anew_part(Scd))),
    })

out = {"p": int(p), "B": int(Bsel), "nE": int(nE), "lam": int(lam),
       "anew_order": int(ANEW), "l0": int(l0), "cof": int(cof),
       "small_ells": [int(q) for q in small_ells if q > 3],
       "n_rational_lifts": int(nlift), "records": records,
       "n14": {"k_multipliers": [], "k_expected_psq_mod_anew": int((p*p) % ANEW),
               "affine_violations": None, "affine_total": None, "hom_holds": None, "hom_total": None}}
fn = "powered_p%d_data.json" % p
with open(fn, "w") as fh: json.dump(out, fh)
distinct_closed = len(set(r["Sclosed_str"] for r in records if r["Sclosed_str"] is not None))
print("WROTE %s | p=%d B=%d nE=%d lam=%d |A_new|=%d=%s | small_ells(>3)=%s | reps=%d | S_closed distinct=%d | %.1fs"
      % (fn, p, Bsel, nE, lam, ANEW, str(Integer(ANEW).factor()),
         [int(q) for q in small_ells if q > 3], nlift, distinct_closed, time.time()-t0))
