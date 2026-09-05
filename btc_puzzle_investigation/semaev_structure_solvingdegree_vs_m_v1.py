#!/usr/bin/env sage
# Route A crux runner (PREREG_semaev_structure_solvingdegree_vs_m_v1.md).
# Q: does the Semaev summation-polynomial COEFFICIENT structure lower the solving degree
#    below a generic system on the SAME monomial support, and does the gap GROW with m?
# All degrees are integers from exact GF(p) Macaulay ranks. No float in the degree read-out.
import sys, json, time
import random as pyr
# Pull in the harness defs (summation_poly, decomposition_system, first_fall_and_solving,
# decomposable_target) WITHOUT triggering its __main__ demo. Runs under `sage <this>.py`,
# so Sage globals (GF, matrix, PolynomialRing, EllipticCurve, prod) are already present.
_ns = dict(globals()); _ns["__name__"] = "semaev_harness"
exec(open("semaev_elimination_v1.py").read(), _ns)
globals().update({k: v for k, v in _ns.items() if not k.startswith("__")})

# ---- exact-integer median (no float): lower-middle of the sorted list -------------------
def imed(vals):
    s = sorted(vals); return s[len(s)//2] if s else None

def quo_and_degrees(F, gens_list, xs, Dmax):
    """0-dim quotient dimension (exact) + (d_ff, d_solv) from Macaulay ranks. None if not 0-dim."""
    Rx = xs[0].parent(); I = Rx.ideal(gens_list)
    dim = int(I.dimension())
    if dim != 0:
        return dim, None, None, None
    q = int(I.vector_space_dimension())
    d_ff, d_solv, _ = first_fall_and_solving(F, gens_list, xs, Dmax, q)
    return dim, q, d_ff, d_solv

def build_generic(F, m, tval, Vroots, Sx_gens, planted, seed):
    """Same field eqs + a random-coefficient poly on the EXACT monomial support of Sx,
    forced to vanish at the planted decomposition (subtract the constant it takes there)."""
    Rx = Sx_gens[0].parent()
    Sx = Sx_gens[0]; field_eqs = Sx_gens[1:]
    rng = pyr.Random(seed); pchar = int(F.characteristic())
    G = Rx(0)
    for mon in Sx.monomials():
        G += F(rng.randrange(1, pchar)) * mon          # nonzero random coeff, same support
    val = G(*[F(v) for v in planted])                   # constant it takes at the plant
    G = G - val                                         # force G(plant) = 0 (support-preserving up to const term)
    return [G] + field_eqs

def run_m(F, A, B, m, Dmax, K_null, seed0):
    out = {"m": m, "p": int(F.characteristic())}
    tgt = decomposable_target(F, A, B, m, extra=0, seed=seed0)
    if tgt is None:
        out["status"] = "no_decomposable_target"; return out
    tval, Vroots = tgt
    planted = list(Vroots)                               # |V| = m ; planted tuple = the m decomposition x-coords
    Rx, gens_list, xs = decomposition_system(F, A, B, m, tval, Vroots)
    # ---- Semaev (true coefficients) --------------------------------------------------------
    t0 = time.time()
    dimS, qS, dffS, dsolvS = quo_and_degrees(F, gens_list, xs, Dmax)
    out["semaev"] = {"dim": dimS, "quo": qS, "d_ff": dffS, "d_solv": dsolvS, "sec": int(time.time()-t0)}
    if qS is None:
        out["status"] = "semaev_not_0dim"; return out
    # ---- firing controls (read-out calibration at KNOWN low solving degrees) ---------------
    lin = [xi - F(v) for xi, v in zip(xs, planted)]      # x_i = v_i  -> a single point, d_solv MUST be 1
    _, qL, _, dsolvL = quo_and_degrees(F, lin, xs, Dmax)
    _, qFE, dffFE, dsolvFE = quo_and_degrees(F, list(gens_list[1:]), xs, Dmax)  # field eqs only -> d_solv MUST be m
    out["plant_linear"] = {"quo": qL, "d_solv": dsolvL, "must_be": 1}
    out["plant_fieldeqs_only"] = {"quo": qFE, "d_ff": dffFE, "d_solv": dsolvFE, "must_be": m}
    # ---- generic control: random coeffs on the SAME support, variety-matched ---------------
    gen_dsolv = []; gen_dff = []; drawn = 0; kept = 0
    for k in range(4 * K_null):                          # oversample; keep only variety-matched 0-dim draws
        if kept >= K_null: break
        drawn += 1
        gg = build_generic(F, m, tval, Vroots, gens_list, planted, seed0 * 1000 + k)
        dimG, qG, dffG, dsolvG = quo_and_degrees(F, gg, xs, Dmax)
        if qG is None or qG != qS:                      # Section 7 guard: must be 0-dim AND variety-size-matched
            continue
        if dsolvG is None:                              # exceeded Dmax -> record as wall for this draw
            continue
        kept += 1; gen_dsolv.append(int(dsolvG)); gen_dff.append(None if dffG is None else int(dffG))
    out["generic"] = {"drawn": drawn, "kept": kept,
                      "d_solv_min": (min(gen_dsolv) if gen_dsolv else None),
                      "d_solv_med": imed(gen_dsolv),
                      "d_solv_max": (max(gen_dsolv) if gen_dsolv else None),
                      "d_solv_all": gen_dsolv,
                      "d_ff_all": gen_dff}
    if gen_dsolv and dsolvS is not None:
        out["delta_d_solv_med"] = imed(gen_dsolv) - dsolvS          # >0  => structure EASIER than generic
    out["status"] = "ok"
    return out

def main():
    p = 307; A = 0; B = 7                                # j=0 / secp form; p = 307 = 1 mod 3 (ordinary), M9 scope
    F = GF(p)
    K_null = 6
    results = []
    # m=2,3 tractable; m=4 attempted with a bigger Dmax + is the wall per XI.4
    plan = [(2, 8, 1), (3, 14, 7), (4, 18, 11)]
    for (m, Dmax, seed0) in plan:
        t0 = time.time()
        r = run_m(F, A, B, m, Dmax, K_null, seed0)
        r["wall_sec"] = int(time.time() - t0)
        results.append(r)
        print("---- m=%d  (%.0fs) ----" % (m, time.time()-t0))
        print(json.dumps(r, indent=2, default=str))
        sys.stdout.flush()
    with open("scratchpad/semaev_structure_vs_m_v1_out.json", "w") as fh:
        json.dump(results, fh, indent=2, default=str)
    # ---- compact summary table ----
    print("\n===== SUMMARY: solving degree, Semaev (true coeffs) vs generic (random, same support) =====")
    print(" m | p   | quo | d_solv Semaev | d_solv generic min/med/max | Δmed | plant(lin=1, FEonly=m)")
    for r in results:
        if r.get("status") != "ok":
            print(" %d | %d | -- | status=%s" % (r["m"], r["p"], r.get("status"))); continue
        s = r["semaev"]; g = r["generic"]
        print(" %d | %d | %s | %s | %s/%s/%s | %s | lin=%s FE=%s" % (
            r["m"], r["p"], s["quo"], s["d_solv"],
            g["d_solv_min"], g["d_solv_med"], g["d_solv_max"],
            r.get("delta_d_solv_med"),
            r["plant_linear"]["d_solv"], r["plant_fieldeqs_only"]["d_solv"]))
    print("===== DONE =====")

main()
