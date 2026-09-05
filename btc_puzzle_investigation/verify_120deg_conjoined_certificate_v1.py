#!/usr/bin/env python3
"""verify_120deg_conjoined_certificate_v1.py -- the 120deg census certificate, REPAIRED.

THE BUG (CORRECTION_120deg_census_certification_direction_v1.md).
    run_n1_120deg_v1.py reports g = min_l g_l and reads a computed 2 as "g = 2." But reduction only
    RAISES gcd degree, so min_l g_l >= g_true. A computed 0 certifies g_true = 0 exactly; a computed
    2 certifies ONLY g_true <= 2. The census's headline (= 2) is the uncertified direction.

THE REPAIR -- a CONJUNCTION of two exact halves (neither alone yields g = 2):
    (lower, g >= 2)   PART 1 (verify_120deg_symbolic_factorization_v1) PROVED symbolically,
                      e1 and p free, eps = chi2(-1) either sign:
                          e2 = e1^2 - eps*p, e3 = eps*p*e1, e4 = p^2
                          ==> L(T) = D(T)*Dbar(T), L(zeta3 T) = zeta3*(T^2+e1*T+eps*p)*D(T),
                              D(T) = T^2 + zeta3*e1*T + eps*p*zeta3^2  monic, never degenerate
                          ==> deg gcd(L(T), L(zeta3 T)) >= 2  UNCONDITIONALLY  (over Q[eps,p,zeta3][T]).
                      That is a deg-2 common factor over Q(zeta_M)[T] with M = lcm(n,3) -- no embedding
                      or finite-field inflation is in the lower bound. PART 2 (this script's reuse of
                      verify_120deg_exact_certificate_v2.check_identity) measures the one empirical
                      input exactly, per prime, uniform over every cell a != 0:
                          V2(a) - V1(a)^2 = -2*eps*p.
                      A prime "holding" (PART 1 + PART 2) means g >= 2 at EVERY surviving cell of p.
    (upper, g <= 2)   the census min_l g_l == 2 for that cell (run_n1_120deg_v1.g_and_flags).
    Together:        holds(prime)  AND  min_l g_l(cell) == 2   ==>   g_true(cell) == 2  exactly.

This script reuses the existing (correct) machinery; it does NOT recompute V1/V2 or the convolution.
EXACT INTEGER / MODULAR ARITHMETIC ONLY. No float in the signal path. No new ring infrastructure
(the Z[ζ_M] resultant is the purer A2 cross-check, separate).
"""
import sys, time, json

import audit_n1_vsign_v2_core as core
from verify_120deg_exact_certificate_v2 import check_identity as _part2_check_identity
from run_n1_120deg_v1 import (
    mu6_reps, ell_primes, g_and_flags,
    deg_gcd, primitive_root_of_order,
)

# prime strata frozen by run_n1_120deg_v1 / verify_120deg_exact_certificate_v2 (same set).
IN_P = (43, 67, 79, 127, 163, 211, 547)
S_P  = (823, 907, 967, 991, 1051, 1303, 1831, 2143, 2251, 2503)
C_P  = (577, 733, 1237, 1249, 1669)


# ---------- per-prime / per-cell conjoined certificate ----------
def conjoined_prime(p, tag, n_ells=5, budget_s=900, verbose=True):
    """For prime p: lower-bound whole prime, upper-bound per cell, conjoin."""
    t0 = time.time()
    n = core.curve_order(p)
    assert core.is_prime(n), (p, n)
    dl = core.dlog_table(p, n)
    h1 = core.hist_k1(p, n, dl)
    h2 = core.hist_k2(p, n, dl)

    # ---- lower bound (g >= 2): PART 1 (symbolic, unconditional) confirmed by PART 2 (exact) ----
    lower = _part2_check_identity(p, n, h1, h2)        # the per-prime residual
    lower_holds = bool(lower["holds"])                 # uniform over every cell a != 0

    # ---- upper bound (g <= 2): the census min_l g_l, per cell ----
    reps = mu6_reps(n)
    ells = ell_primes(n, n_ells)
    cells = []                                          # per-cell upper-bound record
    n_certified = n_null = n_uncertified = n_abstain = 0
    eps = lower["eps"]
    for a in reps:
        if time.time() - t0 > budget_s:
            n_abstain = len(reps) - len(cells)
            if verbose:
                print(f"  [{tag}] p={p} ABSTAIN (budget {budget_s}s) after {len(cells)}/{len(reps)} cells")
            break
        gmin, is_zero, is_rep = g_and_flags(p, n, h1, h2, a, ells)
        spread = None                                     # per-cell spread max_l g_l - min_l g_l
        # recompute spread cheaply: g_and_flags returns the min; re-walk ells to get the max for the
        # CORRECTION's interim diagnostic (so a reader can see whether the ells agreed).
        gmax = -1
        if not is_zero and not is_rep:
            for l in ells:
                r  = primitive_root_of_order(n, l)
                w  = primitive_root_of_order(3, l)
                inv2 = pow(2, l-2, l)
                ra = pow(r, a % n, l)
                rp = 1; V1 = 0; V2 = 0
                for d in range(n):
                    if h1[d]: V1 = (V1 + h1[d]*rp) % l
                    if h2[d]: V2 = (V2 + h2[d]*rp) % l
                    rp = rp*ra % l
                e1 = (-V1) % l
                e2 = (V1*V1 + V2)*inv2 % l
                leg = 1 if p % 4 == 1 else -1
                e3 = (leg*p*e1) % l
                e4 = (p*p) % l
                L  = [e4, (-e3) % l, e2, (-e1) % l, 1]
                wk = [1, w, w*w % l, pow(w,3,l), pow(w,4,l)]
                Lz = [L[k]*wk[k] % l for k in range(5)]
                gl = deg_gcd(L, Lz, l)
                if gl > gmax: gmax = gl
            spread = gmax - gmin
        # ---- the conjunction ----
        if is_zero:
            # null cell: a computed 0 certifies g_true = 0 EXACTLY (the census's correct direction).
            verdict_cell = "g0_exact"; n_null += 1; certified = True
        elif is_rep:
            verdict_cell = "repeated_root_withheld"; n_uncertified += 1; certified = False
        elif lower_holds and gmin == 2:
            verdict_cell = "g2_exact"; n_certified += 1; certified = True
        else:
            verdict_cell = "NOT_certified"
            n_uncertified += 1; certified = False
        cells.append({"a": a, "min_l_g": gmin if not (is_zero or is_rep) else None,
                      "is_zero": is_zero, "is_repeated": is_rep,
                      "spread_maxmin": spread,
                      "cell_verdict": verdict_cell})

    dt = time.time() - t0
    res = {
        "p": p, "n": n, "tag": tag, "eps": eps, "p_mod_4": p % 4,
        "lower_holds_g_ge_2": lower_holds,          # whole-prime (PART 1 symbolic + PART 2 exact)
        "lower_detail": {k: lower[k] for k in
                         ("const_off_zero", "measured_V2_minus_V1sq", "target_this_branch")},
        "n_cells": len(reps), "n_certified_g2_exact": n_certified,
        "n_null_g0_exact": n_null, "n_uncertified": n_uncertified, "n_abstain": n_abstain,
        "cells": cells, "secs": dt,
        # a prime is "wholly exact" iff lower holds AND every non-null cell is certified g=2.
        "all_cells_exact": (lower_holds and n_uncertified == 0 and n_abstain == 0
                            and (n_certified + n_null) == len(reps)),
    }
    if verbose:
        flag = "ALL EXACT" if res["all_cells_exact"] else "*** NOT all exact ***"
        print(f"  [{tag}] p={p:>5} n={n:>5} p%4={p%4} eps={eps:+d} cells={len(reps):>4} | "
              f"lower(g>=2)={'Y' if lower_holds else 'N'} | "
              f"g2={n_certified} g0={n_null} uncrt={n_uncertified} abst={n_abstain} | {flag} | {dt:.1f}s")
        sys.stdout.flush()
    return res


# ---------- SELF-TEST: the CORRECTION's PLANT-B witness (true g_3 = 0) must NOT certify g = 2 ----
def plant_b_selftest():
    """CORRECTION §2: alpha=3+2i, beta=2+3i (both norm 13), ratio i (not zeta_3) => TRUE g_3 = 0.
    Reduced mod a small l it reads min_l g_l = 2 at l=13, 37 -- the inflation the conjunction must
    catch. We plant it through the SAME deg_gcd routine used by the census and confirm the
    conjoined verdict is 'NOT_certified' (because the lower-bound residual e2 = e1^2 - eps*p does NOT
    hold for this fabricated h2). This is the test that the conjunction is not vacuous.
    """
    # work in F_l with i and zeta_3 present: l == 1 mod 12.
    l = 13
    while not (core.is_prime(l) and (l-1) % 12 == 0): l += 1
    i0 = core.tonelli((l-1) % l, l)
    w  = primitive_root_of_order(3, l); w2 = w*w % l
    alpha = (3 + 2*i0) % l; ca = (3 - 2*i0) % l
    beta  = (2 + 3*i0) % l; cb = (2 - 3*i0) % l
    def poly_from_roots(rs):
        P = [1]
        for rt in rs:
            Q = [0]*(len(P)+1)
            for idx, c in enumerate(P):
                Q[idx]   = (Q[idx]   - c*rt) % l
                Q[idx+1] = (Q[idx+1] + c) % l
            P = Q
        return P
    # PLANT-B: {alpha, beta, -conj(alpha), -conj(beta)} -- ratio beta/alpha = i, NOT zeta_3.
    B = poly_from_roots([alpha, beta, (-ca) % l, (-cb) % l])
    def gof(P):
        wk = [pow(w, k, l) for k in range(len(P))]
        Pz = [P[k]*wk[k] % l for k in range(len(P))]
        return deg_gcd(P, Pz, l)
    g_read = gof(B)                       # the census reading: min_l g_l (here a single l)
    # Does PLANT-B satisfy the algebraic identity e2 = e1^2 - eps*p (eps = chi2(-1) at the "prime")?
    # We check directly: its coefficients e1,e2,e3,e4 give e2 - e1^2; for a genuine 120deg object that
    # equals -eps*p. PLANT-B's eigenvalues are NOT zeta_3-locked, so this must FAIL.
    # B = T^4 - e1 T^3 + e2 T^2 - e3 T + e4  (low->high)
    e1 = (-B[3]) % l
    e2 = B[2] % l
    # pick p = 13 (norm of the factors), eps = chi2(-1) mod 13 = legendre(-1,13): 13 % 4 == 1 -> +1
    p_plant = 13; eps_plant = core.legendre(-1, p_plant)
    residual = (e2 - e1*e1) % l
    target   = (-eps_plant * p_plant) % l
    identity_holds = (residual == target) % l
    # The conjoined verdict: certified g=2 requires identity_holds AND g_read == 2.
    certified = identity_holds and (g_read == 2)
    res = {"l": l, "p_plant": p_plant, "eps_plant": eps_plant,
           "g_read_min_l": g_read, "true_g3": 0,
           "residual_e2_minus_e1sq_mod_l": residual,
           "target_neg_eps_p_mod_l": target,
           "identity_holds": identity_holds,
           "conjoined_certified_g2": certified}
    ok = (g_read == 2) and (not identity_holds) and (not certified)
    print("SELF-TEST (PLANT-B, true g_3 = 0):", res)
    print("   ->", "PASS (census reads 2 BUT conjunction correctly does NOT certify)"
          if ok else "*** FAIL *** (conjunction is vacuous or the witness is wrong)")
    return ok, res


if __name__ == "__main__":
    print("=== SELF-TEST: the conjunction must NOT certify the g_3 = 0 witness ===")
    ok, _ = plant_b_selftest()
    assert ok, "self-test failed: the conjunction would certify a true g=0 object -> HALT"

    out = {"freeze_sha256": "a964f246b87fbe302b4740c3123a40a25ff0376b60cc45f8c3ef14d3c23c9fdf",
           "IN": [], "S": [], "C": []}
    print("\n=== IN-SAMPLE (validation) ===")
    for p in IN_P:
        out["IN"].append(conjoined_prime(p, "IN"))
    print("\n=== STRATUM S (PRIMARY, out-of-sample) ===")
    for p in S_P:
        out["S"].append(conjoined_prime(p, "S "))
    print("\n=== STRATUM C (p == 1 mod 4, eps = +1 branch) ===")
    for p in C_P:
        out["C"].append(conjoined_prime(p, "C "))

    with open("RESULT_120deg_conjoined_certificate_v1.json", "w") as f:
        json.dump(out, f, indent=1)

    def summ(rows):
        done = [r for r in rows if r is not None]
        tot = sum(r["n_cells"] for r in done)
        cert = sum(r["n_certified_g2_exact"] for r in done)
        nul  = sum(r["n_null_g0_exact"] for r in done)
        unc  = sum(r["n_uncertified"] for r in done)
        allx = sum(1 for r in done if r["all_cells_exact"])
        return f"{allx}/{len(done)} primes wholly exact | cells: g2_exact={cert} g0_exact={nul} uncrt={unc} (of {tot})"
    print("\n=== VERDICT (conjoined: PART1 symbolic g>=2 + PART2 exact per-prime + census g<=2 per-cell) ===")
    print("  IN-SAMPLE :", summ(out["IN"]))
    print("  STRATUM S :", summ(out["S"]), " <-- PRIMARY")
    print("  STRATUM C :", summ(out["C"]))
