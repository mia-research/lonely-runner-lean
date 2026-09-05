"""
Exact implementation of PREREG_amicable_log_bridge_v1.md — v2.

v2 fixes, relative to amicable_log_bridge_v1.py, the defects found by the
experiment-designer audit (verdict layer + controls) AND two runtime bugs:

  BUG A (control validity): v1 synthesized reversed non-amicable orientations
    (m,q); for a NON-amicable pair the reverse is not a real curve unit
    (q ≠ #E₇(F_m)) so enumeration never closes → ~half the controls VOIDed.
    v2 uses only genuine (q,#E₇(F_q)) units in their natural orientation.
  BUG B (plant attenuation): v1's plant kept the double-centring term from the
    UN-planted feature while the pairing used the planted feature, so the plant
    partially self-cancelled (ε_min came in ~4–6× coarse vs 3/√n). v2 recomputes
    the centring Σ_F·conj(Σ_g) from the planted feature (exact §3.1 statistic on
    the planted data), which is legitimate because Σ_F is invariant under the
    μ₆-equivariant NULL-A permutation.

Audit fixes wired in:
  §3.2 primary Mann–Whitney contrast now actually invoked (discovery + replication).
  §4.2 NULL-B matched on orientation + stratum + n-window(0.8m..1.25m) + g-marginal
       (as a tie-break preference; residual gap reported; UNMATCHED units flagged,
       never silently stratum-relaxed).
  §5 plant: full ladder incl. 1/250, 1/1000; per-unit ε=1/2 POWER GATE (underpowered
       units excluded from the verdict, counted); SECOND plant = contrast-power check
       (inject ε into the amicable arm, require W to reject, report ε_min^W).
  §6.2 replication decision (sign of W agrees discovery↔replication) computed.

EXACTNESS (§8): no float in the signal path.  check_no_float.py must pass.
"""
import sys, json, time
from fractions import Fraction
import numpy as np
from sympy import isprime, primerange, divisors, primitive_root

from amicable_correspondence_tierA_v1 import (
    canonical_gen, order_E7, enumerate_points, build_frame, vec_modpow,
)
from amicable_log_bridge_v1 import (
    OMEGA_POW, zw_mul, zw_conj, zw_norm, zw_sector,
    cubic_char_setup, cubic_char_vec, mann_whitney,
)

sys.set_int_max_str_digits(100000)


# ---------------------------------------------------------------- orbit assembly
def unit_features(p, n):
    """Build the per-orbit Z[ω] feature/target arrays for one curve, or a VOID reason.
    Returns dict with fa,fb (Fval per orbit), ga,gb (Σ conj g per orbit), Sg, kF,kg,
    norb, plus forced-row status.  All exact int / int64 (bounds < 2^63 for n<2e6)."""
    if not (n % 6 == 1 and (n - 1) % 3 == 0 and (p - 1) % 3 == 0):
        return {"VOID": "forced_frame_predicate"}
    G = canonical_gen(p)
    X, Y = enumerate_points(p, n, G)
    if X[n - 1] == 0 and Y[n - 1] == 0:
        return {"VOID": "enumeration_incomplete"}
    e3p, tabp = cubic_char_setup(p)
    kF = cubic_char_vec(Y, p, e3p, tabp)
    if (kF[1:] < 0).any():
        return {"VOID": "curve_side_zero_y"}
    e3n, tabn = cubic_char_setup(n)
    D = np.arange(0, n, dtype=np.int64)
    rhs = ((D * D % n) * D % n + 7) % n
    kg = cubic_char_vec(rhs, n, e3n, tabn)
    lam = pow(int(primitive_root(n)), (n - 1) // 3, n); lam2 = lam * lam % n
    im1 = D * lam % n; negD = (n - D) % n
    reps = np.minimum.reduce([D, im1, D * lam2 % n, negD, negD * lam % n, negD * lam2 % n])
    fr = {"F_lambda_inv": bool(np.array_equal(kF[im1[1:]], kF[1:])),
          "F_neg_inv":    bool(np.array_equal(kF[negD[1:]], kF[1:])),
          "g_lambda_inv": bool(np.array_equal(kg[im1[1:]], kg[1:]))}
    if not all(fr.values()):
        return {"VOID": "forced_row_failed", "forced_rows": fr}
    uniq, inv = np.unique(reps[1:], return_inverse=True); norb = len(uniq)
    if norb * 6 != n - 1:
        return {"VOID": "orbit_size_not_6"}
    kF_orb = kF[uniq]
    fa = np.array([OMEGA_POW[int(k)][0] for k in kF_orb], np.int64)
    fb = np.array([OMEGA_POW[int(k)][1] for k in kF_orb], np.int64)
    cg_a = np.zeros(n, np.int64); cg_b = np.zeros(n, np.int64)
    for k in (0, 1, 2):
        ca, cb = zw_conj(OMEGA_POW[k]); m = (kg == k); cg_a[m] = ca; cg_b[m] = cb
    ga = np.zeros(norb, np.int64); gb = np.zeros(norb, np.int64)
    np.add.at(ga, inv, cg_a[1:]); np.add.at(gb, inv, cg_b[1:])
    sg_a = sum(int((kg[1:] == k).sum()) * OMEGA_POW[k][0] for k in (0, 1, 2))
    sg_b = sum(int((kg[1:] == k).sum()) * OMEGA_POW[k][1] for k in (0, 1, 2))
    kg_rep = kg[uniq]
    ta = np.array([OMEGA_POW[int(k)][0] if k >= 0 else 0 for k in kg_rep], np.int64)
    tb = np.array([OMEGA_POW[int(k)][1] if k >= 0 else 0 for k in kg_rep], np.int64)
    return {"fa": fa, "fb": fb, "ga": ga, "gb": gb, "Sg": (sg_a, sg_b),
            "ta": ta, "tb": tb, "norb": norb, "n": n, "kF": kF, "kg": kg,
            "forced_rows": fr, "reps": uniq, "inv": inv}


def N_of(fa, fb, ga, gb, Sg, n):
    """N(T) for feature (fa,fb) with centring recomputed FROM this feature (exact §3.1)."""
    SF = (6 * int(fa.sum()), 6 * int(fb.sum()))
    CA, CB = zw_mul(SF, zw_conj(Sg))
    pa = int(np.sum(fa * ga - fb * gb)); pb = int(np.sum(fa * gb + fb * ga - fb * gb))
    return zw_norm(((n - 1) * pa - CA, (n - 1) * pb - CB)), ((n - 1) * pa - CA, (n - 1) * pb - CB)


def perm_pvalue(fa, fb, ga, gb, Sg, n, N_base, M, rng):
    """π = (1+#{N(T^σ) ≥ N_base})/(M+1) under μ₆-equivariant NULL-A (orbit relabel).
    Centring is invariant under the permutation (Σ_F fixed), computed once."""
    SF = (6 * int(fa.sum()), 6 * int(fb.sum())); CA, CB = zw_mul(SF, zw_conj(Sg))
    norb = len(fa); ge = 0
    for _ in range(M):
        pm = rng.permutation(norb); fap = fa[pm]; fbp = fb[pm]
        pa = int(np.sum(fap * ga - fbp * gb)); pb = int(np.sum(fap * gb + fbp * ga - fbp * gb))
        if zw_norm(((n - 1) * pa - CA, (n - 1) * pb - CB)) >= N_base:
            ge += 1
    return ge + 1, M + 1


# ---------------------------------------------------------------- per-unit run
def run_unit(p, n, M=9999, M_power=999, seed=0):
    """Real statistic + structural readouts + ε=1/2 POWER GATE (correct centring)."""
    out = {"p": p, "n": n, "orientation": "p<n" if p < n else "p>n",
           "stratum": {"9_div_p1": (p - 1) % 9 == 0, "9_div_n1": (n - 1) % 9 == 0,
                       "p_mod4": p % 4}}
    F = unit_features(p, n)
    if "VOID" in F:
        out["VOID"] = F["VOID"]; return out
    fa, fb, ga, gb, Sg, n_ = F["fa"], F["fb"], F["ga"], F["gb"], F["Sg"], n
    out["norbits"] = F["norb"]; out["forced_rows"] = F["forced_rows"]
    N_base, T = N_of(fa, fb, ga, gb, Sg, n_)
    out["N_T"] = N_base; out["T"] = list(T); out["T_sector"] = zw_sector(*T)
    out["R_num"], out["R_den"] = N_base, (n - 1) * (n - 1) * n
    rng = np.random.default_rng(seed)
    out["pi_num"], out["pi_den"] = perm_pvalue(fa, fb, ga, gb, Sg, n_, N_base, M, rng)
    # ε=1/2 POWER GATE (single replicate, correct centring): powered iff π_plant ≤ 0.005
    ta, tb = F["ta"], F["tb"]; norb = F["norb"]
    rngp = np.random.default_rng(seed ^ 0x5EED)
    order = rngp.permutation(norb); sel = order[:norb // 2]
    fap = fa.copy(); fbp = fb.copy(); fap[sel] = ta[sel]; fbp[sel] = tb[sel]
    Np, _ = N_of(fap, fbp, ga, gb, Sg, n_)
    pn, pd = perm_pvalue(fap, fbp, ga, gb, Sg, n_, Np, M_power, rngp)
    out["power_half_pi_num"], out["power_half_pi_den"] = pn, pd
    out["powered"] = Fraction(pn, pd) <= Fraction(5, 1000)
    # §3.3-2 contingency
    kF, kg = F["kF"], F["kg"]
    out["contingency_Fg"] = [[int(((kF[1:] == i) & (kg[1:] == j)).sum()) for j in (0,1,2)]
                             for i in (0,1,2)]
    return out


# ---------------------------------------------------------------- plant (§5)
def plant_ladder_run(p, n, ladder, reps=30, M=1999, base_seed=1000):
    """Firing ladder with CORRECT centring.  Detected(ε)=π≤1/200 in ≥24/reps."""
    F = unit_features(p, n)
    if "VOID" in F:
        return {"VOID": F["VOID"]}
    fa0, fb0, ga, gb, Sg = F["fa"], F["fb"], F["ga"], F["gb"], F["Sg"]
    ta, tb, norb = F["ta"], F["tb"], F["norb"]
    res = {}; eps_min = None
    for (num, den) in ladder:
        mp = num * norb // den; hits = 0
        for r in range(reps):
            rng = np.random.default_rng(base_seed + 7919 * num * 10007 + 31 * den + r)
            sel = rng.permutation(norb)[:mp]
            fa = fa0.copy(); fb = fb0.copy(); fa[sel] = ta[sel]; fb[sel] = tb[sel]
            Np, _ = N_of(fa, fb, ga, gb, Sg, n)
            pn, pd = perm_pvalue(fa, fb, ga, gb, Sg, n, Np, M, rng)
            if Fraction(pn, pd) <= Fraction(5, 1000):
                hits += 1
        fires = hits >= (24 * reps) // 30
        res[f"{num}/{den}"] = {"planted_orbits": mp, "detected": hits, "reps": reps,
                               "fires": fires}
        if fires:
            eps_min = f"{num}/{den}"
    res["eps_min"] = eps_min
    return res


# ---------------------------------------------------------------- second plant (§5)
def contrast_power_plant(amic_units, ctrl_pis, ladder, M=1999, seed=2000):
    """Inject ε into the AMICABLE arm only; recompute their π; run W vs unchanged
    controls; report smallest ε with two-sided W-rejection at α=0.01 (ε_min^W).
    ctrl_pis: list of (num,den) π for the control arm (unchanged)."""
    out = {}; eps_min_W = None
    feats = []
    for (p, n) in amic_units:
        F = unit_features(p, n)
        if "VOID" not in F:
            feats.append((p, n, F))
    for (num, den) in ladder:
        planted_pis = []
        for (p, n, F) in feats:
            fa0, fb0, ga, gb, Sg = F["fa"], F["fb"], F["ga"], F["gb"], F["Sg"]
            ta, tb, norb = F["ta"], F["tb"], F["norb"]
            rng = np.random.default_rng(seed + num * 101 + den + (p % 9973))
            mp = num * norb // den; sel = rng.permutation(norb)[:mp]
            fa = fa0.copy(); fb = fb0.copy(); fa[sel] = ta[sel]; fb[sel] = tb[sel]
            Np, _ = N_of(fa, fb, ga, gb, Sg, n)
            planted_pis.append(perm_pvalue(fa, fb, ga, gb, Sg, n, Np, M, rng))
        mw = mann_whitney(planted_pis, ctrl_pis, resamples=100000, seed=7)
        rej = Fraction(mw["p_two_num"], mw["p_two_den"]) <= Fraction(1, 100)
        out[f"{num}/{den}"] = {"W_p_num": mw["p_two_num"], "W_p_den": mw["p_two_den"],
                               "sign": mw["sign"], "rejects_0.01": rej}
        if rej:
            eps_min_W = f"{num}/{den}"
    out["eps_min_W"] = eps_min_W
    return out


# ---------------------------------------------------------------- NULL-B controls
def g_marginal(n):
    """(#{g=1},#{g=ω},#{g=ω²}) over d=1..n-1 — exact integer counts, cheap char sum."""
    e3n, tabn = cubic_char_setup(n)
    D = np.arange(0, n, dtype=np.int64)
    kg = cubic_char_vec(((D * D % n) * D % n + 7) % n, n, e3n, tabn)
    return tuple(int((kg[1:] == k).sum()) for k in (0, 1, 2))


def matched_controls(amic, nonamic):
    """§4.2 NULL-B on GENUINE non-amicable units (natural orientation only).
    Match on orientation + stratum(9|p-1,9|n-1,p mod4) + n-window[0.8m,1.25m];
    g-marginal used as tie-break (report residual gap); flag UNMATCHED, never
    silently drop the stratum."""
    def strat(q, m): return ((q - 1) % 9 == 0, (m - 1) % 9 == 0, q % 4)
    def gap(g1, g2):                       # max relative gap ×1000 (integer)
        s1 = sum(g1); s2 = sum(g2)
        return max(abs(a * s2 - b * s1) * 1000 // max(1, s1 * s2) for a, b in zip(g1, g2))
    gm = {}                                # lazy g-marginal cache
    def GM(u):
        if u not in gm: gm[u] = g_marginal(u[1])
        return gm[u]
    used = set(); pairs = []; unmatched = []
    for (q, m) in sorted(amic):
        cand = [z for z in nonamic if z[0] not in used
                and ((z[0] < z[1]) == (q < m)) and strat(z[0], z[1]) == strat(q, m)
                and 5 * z[1] >= 4 * m and 4 * z[1] <= 5 * m]   # 0.8m ≤ n_ctrl ≤ 1.25m
        if not cand:
            unmatched.append((q, m)); continue
        gq = GM((q, m))
        best = min(cand, key=lambda z: (gap(gq, GM(z)), abs(z[1] - m), z[0]))
        used.add(best[0])
        pairs.append(((q, m), best, gap(gq, GM(best))))
    return pairs, unmatched


# ---------------------------------------------------------------- orchestration
def band(q): return "discovery" if q < 50000 else ("replication" if q < 200000 else "oos")


if __name__ == "__main__":
    LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
    t0 = time.time()
    print(f"[{time.time()-t0:.0f}s] building frame up to {LIMIT} ...", flush=True)
    amic, nonamic = build_frame(LIMIT)
    amic = sorted(set((q, m) for q, m in amic))            # already both orientations
    nonamic = sorted(set((q, m) for q, m in nonamic))      # GENUINE units only (BUG A fix)
    pairs, unmatched = matched_controls(amic, nonamic)
    print(f"[{time.time()-t0:.0f}s] {len(amic)} amic orientations, {len(pairs)} matched "
          f"pairs, {len(unmatched)} UNMATCHED, {len(nonamic)} genuine nonamic pool",
          flush=True)

    out = {"limit": LIMIT, "pairs": [], "unmatched": unmatched, "plant": {}}
    amic_runs = {}; ctrl_runs = {}
    for i, ((q, m), (cq, cm), ggap) in enumerate(pairs):
        ra = run_unit(q, m, seed=(q * 1000003 + m) % (2**32))
        rc = run_unit(cq, cm, seed=(cq * 1000003 + cm) % (2**32))
        ra["band"] = band(q); rc["band"] = band(cq); ra["arm"] = "amic"; rc["arm"] = "ctrl"
        ra["gmargin_gap_x1000"] = ggap
        amic_runs[(q, m)] = ra; ctrl_runs[(cq, cm)] = rc
        out["pairs"].append({"amic": ra, "ctrl": rc, "ctrl_unit": [cq, cm],
                             "gmargin_gap_x1000": ggap})
        if i % 15 == 0:
            astat = ("VOID:" + ra["VOID"]) if "VOID" in ra else \
                    ("pi=%d/%d pow=%s" % (ra["pi_num"], ra["pi_den"], ra.get("powered")))
            cstat = ("VOID:" + rc["VOID"]) if "VOID" in rc else "ok"
            print(f"  [{i+1}/{len(pairs)}] amic p={q} n={m} {astat} | ctrl p={cq} {cstat} "
                  f"({time.time()-t0:.0f}s)", flush=True)

    # ---- §3.2 PRIMARY Mann–Whitney contrast, powered units only, per band ----
    def contrast(bnd):
        a = [(r["pi_num"], r["pi_den"]) for r in amic_runs.values()
             if r.get("band") == bnd and "VOID" not in r and r.get("powered")]
        c = [(r["pi_num"], r["pi_den"]) for r in ctrl_runs.values()
             if r.get("band") == bnd and "VOID" not in r and r.get("powered")]
        if len(a) < 3 or len(c) < 3:
            return {"band": bnd, "n_amic": len(a), "n_ctrl": len(c), "note": "underpowered/too few"}
        mw = mann_whitney(a, c, resamples=1000000, seed=42); mw["band"] = bnd
        mw["n_amic"], mw["n_ctrl"] = len(a), len(c); return mw
    out["contrast_discovery"] = contrast("discovery")
    out["contrast_replication"] = contrast("replication")
    dW, rW = out["contrast_discovery"], out["contrast_replication"]
    out["replication_decision"] = {
        "sign_discovery": dW.get("sign"), "sign_replication": rW.get("sign"),
        "signs_agree": dW.get("sign") == rW.get("sign") and dW.get("sign") is not None}
    print(f"[{time.time()-t0:.0f}s] contrast discovery={dW} replication={rW}", flush=True)

    # ---- power accounting ----
    pw = {bnd: {"amic_powered": sum(1 for r in amic_runs.values() if r.get("band")==bnd and r.get("powered")),
                "amic_total": sum(1 for r in amic_runs.values() if r.get("band")==bnd and "VOID" not in r),
                "ctrl_powered": sum(1 for r in ctrl_runs.values() if r.get("band")==bnd and r.get("powered")),
                "ctrl_total": sum(1 for r in ctrl_runs.values() if r.get("band")==bnd and "VOID" not in r)}
          for bnd in ("discovery", "replication")}
    out["power_accounting"] = pw
    print(f"[{time.time()-t0:.0f}s] power: {pw}", flush=True)

    # ---- §5 plant firing ladder on size-spread sample (VOID gate: fire at ε=1/2) ----
    LADDER = [(1,2),(1,4),(1,10),(1,25),(1,50),(1,100),(1,250),(1,1000)]
    amic_ok = [u for u, r in amic_runs.items() if "VOID" not in r and r.get("powered")]
    by_n = sorted(amic_ok, key=lambda qm: qm[1])
    sample = [by_n[k] for k in (0, len(by_n)//3, 2*len(by_n)//3, len(by_n)-1)] if by_n else []
    print(f"[{time.time()-t0:.0f}s] plant ladder on {len(sample)} powered sample units "
          f"(M_plant=1999) ...", flush=True)
    fire_half_all = True
    for (q, m) in sample:
        pf = plant_ladder_run(q, m, LADDER, reps=30, M=1999)
        out["plant"][f"{q},{m}"] = pf
        half = pf.get("1/2", {}).get("fires", False); fire_half_all = fire_half_all and half
        print(f"  plant p={q} n={m} eps_min={pf.get('eps_min')} half_fires={half} "
              f"({time.time()-t0:.0f}s)", flush=True)
    out["pipeline_void"] = not fire_half_all      # §9-V: pipeline defect if ε=1/2 fails

    # ---- §5 SECOND plant: contrast power (discovery band) ----
    disc_amic = [u for u, r in amic_runs.items() if r.get("band")=="discovery"
                 and "VOID" not in r and r.get("powered")]
    disc_ctrl_pi = [(r["pi_num"], r["pi_den"]) for r in ctrl_runs.values()
                    if r.get("band")=="discovery" and "VOID" not in r and r.get("powered")]
    if len(disc_amic) >= 3 and len(disc_ctrl_pi) >= 3:
        print(f"[{time.time()-t0:.0f}s] contrast-power plant on {len(disc_amic)} disc amic ...",
              flush=True)
        out["contrast_power_plant"] = contrast_power_plant(
            disc_amic, disc_ctrl_pi, [(1,2),(1,4),(1,10),(1,25),(1,50)])
        print(f"[{time.time()-t0:.0f}s] eps_min^W = {out['contrast_power_plant'].get('eps_min_W')}",
              flush=True)

    with open(f"amicable_log_bridge_v2_results_{LIMIT}.json", "w") as f:
        json.dump(out, f, default=lambda o: list(o) if isinstance(o, tuple) else o)
    print(f"[{time.time()-t0:.0f}s] wrote amicable_log_bridge_v2_results_{LIMIT}.json", flush=True)
