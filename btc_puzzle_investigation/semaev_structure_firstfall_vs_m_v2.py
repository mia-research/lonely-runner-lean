#!/usr/bin/env sage
# Route A crux runner v2 (PREREG_semaev_structure_firstfall_vs_m_v2.md).
# First-fall degree d_ff of {P(x1..xm; t)=0} U {prod(xi-v)=0}, P over a 3-rung ladder:
#   semi-regular (per-monomial random) -> symmetric (one coeff per S_m orbit) -> Semaev (true).
# d_ff = leading-form property (variety-free). All degrees exact GF(p) integer Macaulay ranks.
import sys, json, time
import random as pyr
_ns = dict(globals()); _ns["__name__"] = "semaev_harness"
exec(open("semaev_elimination_v1.py").read(), _ns)
globals().update({k: v for k, v in _ns.items() if not k.startswith("__")})

def imed(vals):
    s = sorted([v for v in vals if v is not None]); return s[len(s)//2] if s else None

def d_ff_of(F, gens_list, xs, Dmax):
    """first D with a genuine degree fall among leading forms; None if none <= Dmax (CENSORED)."""
    stats = macaulay_stats(F, gens_list, xs, Dmax)
    for D in sorted(stats):
        if stats[D].get('fall', 0) > 0:
            return int(D)
    return None

def build_pieces(F, A, B, m, tau, V):
    """Sx (Semaev, t=tau), the shared support, field eqs, and the x-ring."""
    S, xs_big, t_big = summation_poly(F, A, B, m)
    Rt = xs_big[0].parent()
    Rx = PolynomialRing(F, ['x%d' % i for i in range(1, m + 1)], order='degrevlex')
    phi = Rt.hom(list(Rx.gens()) + [F(tau)], Rx)
    Sx = phi(S)
    xr = list(Rx.gens())
    field_eqs = [prod([xi - F(v) for v in V]) for xi in xr]
    return Rx, Sx, xr, field_eqs

def semiregular_P(Rx, F, support, rng, pchar):
    P = Rx(0)
    for mon in support:
        P += F(rng.randrange(1, pchar)) * mon
    return P

def symmetric_P(Rx, F, support, rng, pchar):
    """one random coeff per S_m-orbit (orbit key = sorted exponent vector) -> S_m-symmetric."""
    orbit = {}; P = Rx(0)
    for mon in support:
        key = tuple(sorted(mon.exponents()[0]))
        if key not in orbit:
            orbit[key] = F(rng.randrange(1, pchar))
        P += orbit[key] * mon
    return P

def run_m(F, A, B, m, tau, V, Dmax, K_null, seed0):
    pchar = int(F.characteristic())
    out = {"m": m, "p": pchar, "Dmax": Dmax, "K_null": K_null, "|V|": len(V)}
    Rx, Sx, xr, field_eqs = build_pieces(F, A, B, m, tau, V)
    support = list(Sx.monomials())
    out["n_support"] = len(support)
    # ---- Semaev (true) ----
    out["semaev_dff"] = d_ff_of(F, [Sx] + field_eqs, xr, Dmax)
    # ---- calibrations ----
    out["CAL_A_fieldeqs_only_dff"] = d_ff_of(F, list(field_eqs), xr, Dmax)          # must be None (regular)
    out["CAL_B_linearplant_dff"]  = d_ff_of(F, [xr[0] - F(V[0])] + field_eqs, xr, Dmax)  # must be finite, <= |V|
    # ---- ladder distributions ----
    semi = []; symm = []
    for k in range(K_null):
        rng = pyr.Random(seed0 * 10007 + k)
        semi.append(d_ff_of(F, [semiregular_P(Rx, F, support, rng, pchar)] + field_eqs, xr, Dmax))
        rng2 = pyr.Random(seed0 * 20011 + k)
        symm.append(d_ff_of(F, [symmetric_P(Rx, F, support, rng2, pchar)] + field_eqs, xr, Dmax))
    out["semireg_dff"] = {"all": semi, "median": imed(semi),
                          "censored": sum(1 for v in semi if v is None)}
    out["symm_dff"]    = {"all": symm, "median": imed(symm),
                          "censored": sum(1 for v in symm if v is None)}
    sm = out["semaev_dff"]; symed = imed(symm); sgmed = imed(semi)
    out["delta1_symmetry"]   = (None if (sgmed is None or symed is None) else sgmed - symed)  # semi-reg - symmetric
    out["delta2_coeff"]      = (None if (symed is None or sm is None) else symed - sm)         # symmetric - Semaev
    smin = min([v for v in symm if v is not None], default=None)
    out["semaev_below_all_symmetric"] = (None if (smin is None or sm is None) else bool(sm <= smin))
    return out

def main():
    A = 0; B = 7
    stages = []
    for p in (307, 2069):
        F = GF(p); G = EllipticCurve(F, [A, B]).gens()[0]; tau = int(G[0])
        for (m, Dmax, K) in [(2, 12, 12), (3, 22, 12)]:
            t0 = time.time()
            V = [i for i in range(1, m + 1)]
            r = run_m(F, A, B, m, tau, V, Dmax, K, seed0=m + p)
            r["wall_sec"] = int(time.time() - t0)
            stages.append(r); print(json.dumps(r, default=str)); sys.stdout.flush()
    # m=4 attempt: p=307 only, reduced K, big Dmax; may CENSOR (the XI.4 wall)
    F = GF(307); G = EllipticCurve(F, [A, B]).gens()[0]; tau = int(G[0])
    t0 = time.time(); V = [1, 2, 3, 4]
    r = run_m(F, A, B, 4, tau, V, Dmax=30, K_null=6, seed0=4 + 307)
    r["wall_sec"] = int(time.time() - t0)
    stages.append(r); print(json.dumps(r, default=str)); sys.stdout.flush()
    with open("scratchpad/semaev_structure_firstfall_v2_out.json", "w") as fh:
        json.dump(stages, fh, indent=2, default=str)
    print("\n===== LADDER SUMMARY: first-fall degree d_ff =====")
    print(" p | m | support | Semaev | symmetric(med) | semi-reg(med) | d1=symmetry | d2=coeff | CAL_A/CAL_B")
    for r in stages:
        print(" %d | %d | %d | %s | %s | %s | %s | %s | %s/%s" % (
            r["p"], r["m"], r["n_support"], r["semaev_dff"],
            r["symm_dff"]["median"], r["semireg_dff"]["median"],
            r["delta1_symmetry"], r["delta2_coeff"],
            r["CAL_A_fieldeqs_only_dff"], r["CAL_B_linearplant_dff"]))
    print("===== DONE =====")

main()
