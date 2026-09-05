#!/usr/bin/env sage
# Route A live lead (PREREG_semaev_symmetric_reduction_lastfall_v1.md).
# Does the S_3-symmetric (elementary-symmetric-variable) reduction COLLAPSE the last-fall degree,
# and is any collapse secp-SPECIFIC (Semaev coeffs) or generic (any symmetric coeffs)?
# m=3. Exact GF(p). All degrees integer Macaulay ranks. No float in the degree read-out.
import sys, json, time
import random as pyr
_ns = dict(globals()); _ns["__name__"] = "semaev_harness"
exec(open("semaev_elimination_v1.py").read(), _ns)
globals().update({k: v for k, v in _ns.items() if not k.startswith("__")})

def imed(vals):
    s = sorted([v for v in vals if v is not None]); return s[len(s)//2] if s else None

def last_fall_of(F, gens_list, xs, Dmax):
    """last-fall degree = largest D<=Dmax with a genuine fall; also solving degree via quo target."""
    Rx = xs[0].parent(); I = Rx.ideal(gens_list)
    dim = int(I.dimension())
    if dim != 0:
        return {"dim": dim, "quo": None, "d_ff": None, "d_LF": None, "d_solv": None}
    q = int(I.vector_space_dimension())
    stats = macaulay_stats(F, gens_list, xs, Dmax)
    d_ff = None; d_LF = None; d_solv = None
    for D in sorted(stats):
        s = stats[D]
        if s.get('fall', 0) > 0:
            if d_ff is None: d_ff = int(D)
            d_LF = int(D)                         # last D with a fall (<= Dmax)
        if d_solv is None and s.get('quo') == q:
            d_solv = int(D)
    return {"dim": dim, "quo": q, "d_ff": d_ff, "d_LF": d_LF, "d_solv": d_solv}

def sym_reduce(f, Rx, Rer):
    """Fundamental theorem of symmetric polynomials: f symmetric in x1,x2,x3 (Rx in LEX order) ->
    P in e1,e2,e3 with P(sigma_1,sigma_2,sigma_3) == f. Deterministic, exact."""
    X = Rx.gens(); E1, E2, E3 = Rer.gens()
    s1 = X[0]+X[1]+X[2]; s2 = X[0]*X[1]+X[0]*X[2]+X[1]*X[2]; s3 = X[0]*X[1]*X[2]
    P = Rer(0); g = f
    while g != 0:
        lm = g.lm(); lc = g.lc()
        a, b, c = lm.exponents()[0]                    # symmetric + lex => a>=b>=c
        P += lc * E1**(a-b) * E2**(b-c) * E3**c
        g = g - lc * s1**(a-b) * s2**(b-c) * s3**c
    return P

def build_reduction(F, A, B, tau):
    """Return P(e1,e2,e3) = S4(.,tau) rewritten in elementary-symmetric vars, the e-ring, a
    correctness flag (P(sigma_i(x)) == S4(x,tau)), S4_at_tau, and the x-ring."""
    S3poly, zs, tt = summation_poly(F, A, B, 3)
    Rt = zs[0].parent()
    Rx = PolynomialRing(F, ['x1','x2','x3'], order='lex')   # LEX for sym_reduce leading-term
    X1, X2, X3 = Rx.gens()
    phi2 = Rt.hom([X1, X2, X3, F(tau)], Rx)
    S4_at_tau = phi2(S3poly)                                # symmetric in x1,x2,x3
    Rer = PolynomialRing(F, ['e1','e2','e3'], order='degrevlex')
    P = sym_reduce(S4_at_tau, Rx, Rer)
    E1, E2, E3 = Rer.gens()
    P_back = P.subs({E1: X1+X2+X3, E2: X1*X2+X1*X3+X2*X3, E3: X1*X2*X3})
    ok = bool((P_back - S4_at_tau) == 0)
    return P, Rer, ok, S4_at_tau, Rx

def remainder_eqs(Rer, Vx):
    """r0,r1,r2 in Rer from rem(g, X^3 - e1 X^2 + e2 X - e3), g=prod(X-v), v in Vx."""
    E1,E2,E3 = Rer.gens()
    RerX = PolynomialRing(Rer, 'X'); X = RerX.gen()
    C = X**3 - E1*X**2 + E2*X - E3
    g = prod([X - RerX(Rer(int(v))) for v in Vx])
    rem = g % C
    coeffs = rem.list()                                # [r0, r1, r2, ...]
    while len(coeffs) < 3: coeffs.append(Rer(0))
    return [Rer(coeffs[0]), Rer(coeffs[1]), Rer(coeffs[2])]

def sym_of(vals):
    a,b,c = vals
    return [a+b+c, a*b+a*c+b*c, a*b*c]

def elim_ideal_distinct(F, A, B, tau, Vx):
    """True object: elim_x [ sat( <S4, g(x1),g(x2),g(x3)>, prod(xi-xj) ) ] in F[e1,e2,e3].
    Returns (elim_ideal_in_Rer, unreduced_distinct_quo)."""
    S3poly, zs, tt = summation_poly(F, A, B, 3); Rt = zs[0].parent()
    Rx = PolynomialRing(F, ['x1','x2','x3'], order='degrevlex'); X1,X2,X3 = Rx.gens()
    S4 = Rt.hom([X1,X2,X3,F(tau)], Rx)(S3poly)
    g = lambda xi: prod([xi - F(v) for v in Vx])
    disc = (X1-X2)*(X1-X3)*(X2-X3)
    Iun = Rx.ideal([S4, g(X1), g(X2), g(X3)])
    Isat = Iun.saturation(Rx.ideal([disc]))[0]
    un_quo = int(Isat.vector_space_dimension()) if int(Isat.dimension()) == 0 else None
    # embed into a ring with e's and eliminate x's
    Rb = PolynomialRing(F, ['x1','x2','x3','e1','e2','e3'], order='lex')
    bx = Rb.gens()[:3]; be = Rb.gens()[3:]
    inj = Rx.hom(list(bx), Rb)
    gens_b = [inj(gg) for gg in Isat.gens()] + [
        be[0]-(bx[0]+bx[1]+bx[2]), be[1]-(bx[0]*bx[1]+bx[0]*bx[2]+bx[1]*bx[2]), be[2]-bx[0]*bx[1]*bx[2]]
    J = Rb.ideal(gens_b).elimination_ideal(list(bx))
    Rer = PolynomialRing(F, ['e1','e2','e3'], order='degrevlex')
    proj = Rb.hom([Rer(0)]*3 + list(Rer.gens()), Rer)
    Jer = Rer.ideal([proj(gg) for gg in J.gens()])
    return Jer, un_quo

def decide(a, lo, hi, power_moves):
    """integer order-statistic rule (prereg v2 §E/F, §2)."""
    if not power_moves:
        return "LASTFALL_COEFF_FORCED"
    if a is None or lo is None or hi is None:
        return "UNDEFINED"
    if a < lo:  return "SECP_SPECIFIC"
    if a > hi:  return "ANTI"
    return "GENERIC"

def main():
    A=0; B=7
    out_all = []
    for p in (307, 2069):
        F = GF(p); E = EllipticCurve(F,[A,B]); G = E.gens()[0]; N = int(E.order()); pchar = p
        rng = pyr.Random(1234+p)                                  # FROZEN seed (fix C, I)
        Vx = None; tau = None                                     # plant TWO decomposing triples => reduced quo >= 2
        for _ in range(3000):
            R = int(rng.randrange(1,N))*G
            if R==E(0): continue
            xs=[]; good=True
            for _ in range(2):                                    # each triple sums to R => S4(x1,x2,x3,x(R))=0 (Q4=-R)
                Qa=int(rng.randrange(1,N))*G; Qb=int(rng.randrange(1,N))*G; Qc=R-Qa-Qb
                if E(0) in (Qa,Qb,Qc): good=False; break
                xs += [int(Qa[0]),int(Qb[0]),int(Qc[0])]
            if good and len(set(xs))==6 and int(R[0]) not in set(xs):
                Vx=xs; tau=int(R[0]); break
        planted_e = sym_of([F(v) for v in Vx[:3]])
        P, Rer, ok, S4_at_tau, Rx = build_reduction(F, A, B, tau)
        E1,E2,E3 = Rer.gens()
        r_eqs = remainder_eqs(Rer, Vx)
        rec = {"p": p, "tau": tau, "V": Vx, "|V|": 6, "reduction_correct": ok,
               "P_support": len(P.monomials()), "P_totaldeg": int(P.total_degree())}
        # ---- reduced Semaev + nonemptiness gate ----
        red = last_fall_of(F, [P]+r_eqs, list(Rer.gens()), Dmax=34)
        rec["reduced_semaev"] = red
        rq = red["quo"]
        rec["nonempty_gate"] = (rq is not None and rq >= 2)
        # ---- POWER PROBE (i): membership-only vs +Semaev  (does Ŝ move last-fall?) ----
        memb = last_fall_of(F, list(r_eqs), list(Rer.gens()), Dmax=34)
        rec["probe_i_membership_only"] = memb
        probe_i_moves = bool(memb["d_LF"] != red["d_LF"] or memb["d_solv"] != red["d_solv"])
        # ---- POWER PROBE (iii): constructed plant Ŝ*(e1-1) MUST move last-fall vs reduced ----
        plant = last_fall_of(F, [P*(E1-F(1))]+r_eqs, list(Rer.gens()), Dmax=38)
        rec["probe_iii_plant_Shat_times_e1m1"] = plant
        probe_iii_fires = bool(plant["d_solv"] != red["d_solv"] or plant["d_LF"] != red["d_LF"])
        # ---- symmetric-random-reduced coefficient sweep (does varying Ŝ coeffs move last-fall?) ----
        support = list(P.monomials()); symrand = []
        for k in range(12):
            r2 = pyr.Random(9000+p+k)
            Prand = Rer(0)
            for mon in support:
                Prand += F(r2.randrange(1,pchar))*mon                # uniform NONZERO (fix I)
            Prand = Prand - Prand(planted_e[0],planted_e[1],planted_e[2])   # replant -> consistent
            symrand.append(last_fall_of(F, [Prand]+r_eqs, list(Rer.gens()), Dmax=34)["d_LF"])
        fin = [v for v in symrand if v is not None]
        rec["symrand_reduced_dLF"] = {"all": symrand, "min": (min(fin) if fin else None),
                                      "max": (max(fin) if fin else None),
                                      "distinct": sorted(set(fin))}
        probe_ii_moves = bool(len(set(fin)) > 1)
        rec["power"] = {"probe_i_Shat_moves": probe_i_moves, "probe_ii_coeff_variance": probe_ii_moves,
                        "probe_iii_plant_fires": probe_iii_fires}
        # ---- descriptive: un-reduced (same Dmax=20, fix G) ----
        gX = lambda xi: prod([xi - F(v) for v in Vx])
        X1,X2,X3 = Rx.gens()
        rec["unreduced_descriptive"] = last_fall_of(F, [S4_at_tau, gX(X1), gX(X2), gX(X3)], [X1,X2,X3], Dmax=26)
        # ---- B/D correctness: distinct-saturated variety 6x + ideal equality (GB) ----
        try:
            Jer, un_quo_distinct = elim_ideal_distinct(F, A, B, tau, Vx)
            rec["unreduced_distinct_quo"] = un_quo_distinct
            rec["six_times_check"] = bool(un_quo_distinct is not None and rq is not None and un_quo_distinct == 6*rq)
            rec["ideal_equal_GB"] = bool(Rer.ideal([P]+r_eqs) == Jer)
        except Exception as e:
            rec["unreduced_distinct_quo"] = None; rec["six_times_check"] = None
            rec["ideal_equal_GB"] = "err:%s" % repr(e)[:60]
        # ---- decision (power-gated integer order statistics) ----
        power_moves = probe_i_moves or probe_ii_moves
        a = red["d_LF"]; lo = rec["symrand_reduced_dLF"]["min"]; hi = rec["symrand_reduced_dLF"]["max"]
        rec["VOID_readout_blind"] = (not probe_iii_fires)
        rec["outcome_at_p"] = ("VOID" if not probe_iii_fires else
                               ("VOID_empty" if not rec["nonempty_gate"] else decide(a, lo, hi, power_moves)))
        out_all.append(rec); print(json.dumps(rec, default=str)); sys.stdout.flush()
    with open("scratchpad/semaev_symred_v2_out.json","w") as fh:
        json.dump(out_all, fh, indent=2, default=str)
    # cross-p aggregation (fix I): outcome must agree at both primes
    outcomes = [r["outcome_at_p"] for r in out_all]
    agg = outcomes[0] if len(set(outcomes))==1 else ("INCONCLUSIVE_split:%s" % outcomes)
    print("\n===== SYMMETRIC-REDUCTION LAST-FALL (v2, power-gated) =====")
    print(" p | ok | 6x | idealEq | reduced(dff,dLF,dsolv,quo) | membOnly(dLF,dsolv) | symrand dLF distinct | plant(dLF,dsolv) | power[i,ii,iii] | outcome")
    for r in out_all:
        rs=r["reduced_semaev"]; mb=r["probe_i_membership_only"]; pl=r["probe_iii_plant_Shat_times_e1m1"]; pw=r["power"]
        print(" %d | %s | %s | %s | (%s,%s,%s,%s) | (%s,%s) | %s | (%s,%s) | [%s,%s,%s] | %s" % (
            r["p"], r["reduction_correct"], r["six_times_check"], r["ideal_equal_GB"],
            rs["d_ff"],rs["d_LF"],rs["d_solv"],rs["quo"], mb["d_LF"],mb["d_solv"],
            r["symrand_reduced_dLF"]["distinct"], pl["d_LF"],pl["d_solv"],
            pw["probe_i_Shat_moves"],pw["probe_ii_coeff_variance"],pw["probe_iii_plant_fires"], r["outcome_at_p"]))
    print("AGGREGATE (both primes must agree):", agg)
    print("===== DONE =====")

main()
