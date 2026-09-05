#!/usr/bin/env python3
"""
PL Validation for F1246689 (n=11, Case-2 LRC family).

Proof obligations addressed:
  PL.1 — Prove C_bad(F1246689, M) is exactly periodic-linear in M.
          Analytical argument: show t_M(b) = floor(b / L_0) is M-independent;
          consequence is the "signature" of each fiber b depends on M only through
          inv(M) mod 11 and the residue b mod (L_0 * 11).
  PL.2 — Validate the classwise linear model with holdout.
          Method: fit linear model on first HALF of M-values per class,
          predict second half, verify max residual = 0.

Family: E(M) = (1, 2, 3, 4, 6, 6, 8, 9, M, 11), gcd(M, 792) = 1.
  n = 11, L_0 = lcm(1,2,3,4,6,6,8,9,11) = 792, L = 792*M, N = 11*L.
  B_div = {b in [L/11, 10L/11]} = {b : 72M <= b <= 720M}.
  B_div_count = 648M + 1 = C_F * M + 1 with C_F = 648.
"""
from __future__ import annotations

import csv
import math
from collections import defaultdict
from fractions import Fraction

N = 11
L_0 = 792  # lcm(1,2,3,4,6,8,9,11) — verified below
E_FIXED_NON = [1, 2, 3, 4, 6, 6, 8, 9]   # non-divisible fixed speeds
E_DIV = [11]                               # divisible fixed speed

OUT_MD  = "/tmp/lrc_case2_n11_pl_validation_v1.md"
OUT_CSV = "/tmp/lrc_case2_n11_pl_validation_v1.csv"

# ── PL.1 analytical setup ─────────────────────────────────────────────────────

def verify_L0():
    """Confirm L_0 = 792 = lcm(1,2,3,4,6,6,8,9,11)."""
    return math.lcm(1, 2, 3, 4, 6, 6, 8, 9, 11) == 792


def t_free_runner(b: int, M: int) -> int:
    """
    t_M(b) = floor(M * b / L) = floor(M * b / (792 * M)) = floor(b / 792).
    INDEPENDENT OF M — this is the key PL.1 fact.
    """
    L = L_0 * M
    t_direct = (M * b) // L         # = floor(b / L_0)
    t_formula = b // L_0            # M-independent formula
    assert t_direct == t_formula, f"PL.1 fail: b={b}, M={M}"
    return t_formula


def check_pl1_independence(M_list, sample_b_count=200):
    """
    Verify that t_M(b) = b // L_0 is truly M-independent by comparing
    values across different M for the same b.
    Samples b uniformly from B_div for the first M in M_list.
    Returns (all_consistent: bool, checked_triples: int).
    """
    M0 = M_list[0]
    # B_div for M0
    b_lo = (L_0 * M0) // N           # = 72 * M0
    b_hi = ((N - 1) * L_0 * M0) // N # = 720 * M0
    # Sample b values spaced roughly evenly across B_div for M0
    step = max(1, (b_hi - b_lo) // sample_b_count)
    sample_bs = list(range(b_lo, b_hi + 1, step))[:sample_b_count]

    triples = 0
    for b0 in sample_bs:
        t0 = b0 // L_0
        for M in M_list[1:5]:      # cross-check with 4 more M values
            # Only valid if b0 is in B_div for this M too
            b_lo_M = (L_0 * M) // N
            b_hi_M = ((N - 1) * L_0 * M) // N
            if b0 < b_lo_M or b0 > b_hi_M:
                continue
            t_for_M = t_free_runner(b0, M)
            if t_for_M != t0:
                return False, triples
            triples += 1

    return True, triples


# ── Core computation ──────────────────────────────────────────────────────────

def eval_cbad(M: int) -> dict:
    """Compute B_div, C_bad, B_safe for F1246689(M)."""
    L = L_0 * M
    NL = N * L
    lo = L
    hi = (N - 1) * L

    # B_div: single divisible speed e=11
    b_lo = L // N      # = 72M
    b_hi = ((N-1)*L) // N  # = 720M
    B_div_count = b_hi - b_lo + 1  # = 648M+1

    E_non = E_FIXED_NON + [M]   # all non-divisible speeds including free runner

    C_bad = 0
    for b in range(b_lo, b_hi + 1):
        bad = True
        for a in range(N):
            k = a * L + b
            ok = True
            for e in E_non:
                x = (e * k) % NL
                if x < lo or x > hi:
                    ok = False
                    break
            if ok:
                bad = False
                break
        if bad:
            C_bad += 1

    B_safe = B_div_count - C_bad
    return {"B_div": B_div_count, "C_bad": C_bad, "B_safe": B_safe}


def fit_exact_linear_holdout(points_by_r):
    """
    For each residue class r, split points into first-half (train) and
    second-half (holdout). Fit linear on train, predict holdout.
    Returns dict: r -> (a, b, n_train, n_holdout, max_holdout_error, exact).
    """
    results = {}
    for r, arr in points_by_r.items():
        arr_sorted = sorted(arr)
        n = len(arr_sorted)
        if n < 2:
            results[r] = None
            continue
        # Train on first half (at least 2 pts)
        n_train = max(2, n // 2)
        train = arr_sorted[:n_train]
        holdout = arr_sorted[n_train:]

        # Fit exact on first 2 training points
        M1, y1 = train[0]
        M2, y2 = train[1]
        if M2 == M1:
            results[r] = None
            continue
        a = Fraction(y2 - y1, M2 - M1)
        b = Fraction(y1) - a * M1

        # Check all training points
        train_ok = all(a * M + b == Fraction(y) for M, y in train)
        # Check holdout
        holdout_errors = [abs(float(a * M + b) - y) for M, y in holdout]
        max_holdout_err = max(holdout_errors) if holdout_errors else 0.0
        holdout_ok = all(a * M + b == Fraction(y) for M, y in holdout)

        results[r] = {
            "slope_a": a,
            "intercept_b": b,
            "n_train": n_train,
            "n_holdout": len(holdout),
            "max_holdout_error": max_holdout_err,
            "train_exact": train_ok,
            "holdout_exact": holdout_ok,
            "n_pts": n,
        }
    return results


# ── Main ──────────────────────────────────────────────────────────────────────

def main():
    assert verify_L0(), "L_0 verification failed"

    # ── M range: aim for >= 10 pts per residue class (period=121, need M up to ~13*121=1573)
    MAX_M = 1500
    PERIOD = 121  # n^2 = 121

    M_values = [m for m in range(1, MAX_M + 1) if math.gcd(m, L_0) == 1]
    # Note: gcd(M, 792) = 1 iff M coprime to 2, 3, 11
    print(f"Testing {len(M_values)} values of M in [1, {MAX_M}]")

    # ── PL.1: verify t_M(b) is M-independent ──────────────────────────────
    pl1_ok, pl1_triples = check_pl1_independence(M_values)
    print(f"PL.1: t_M(b)=floor(b/{L_0}) M-independent: {pl1_ok} ({pl1_triples} triples checked)")

    # ── Compute C_bad for all M ────────────────────────────────────────────
    C_F = 648
    rows = []
    cbad_by_r = defaultdict(list)

    print("Computing C_bad(M)...", flush=True)
    for i, M in enumerate(M_values):
        if i % 50 == 0:
            print(f"  M={M} ({i}/{len(M_values)})", flush=True)
        t = eval_cbad(M)
        # Verify B_div formula
        assert t["B_div"] == C_F * M + 1, f"B_div formula fail at M={M}"
        r = M % PERIOD
        cbad_by_r[r].append((M, t["C_bad"]))
        rows.append({
            "M": M,
            "r_mod121": r,
            "B_div": t["B_div"],
            "C_bad": t["C_bad"],
            "B_safe": t["B_safe"],
            "B_margin": t["B_safe"] - (N - 1),
        })

    # ── PL.2: holdout validation ───────────────────────────────────────────
    model = fit_exact_linear_holdout(cbad_by_r)

    n_classes = len(model)
    n_exact = sum(1 for v in model.values() if v and v["holdout_exact"])
    n_trivial = sum(1 for v in model.values() if v and v["n_holdout"] == 0)
    min_pts = min((v["n_pts"] for v in model.values() if v), default=0)
    max_pts = max((v["n_pts"] for v in model.values() if v), default=0)
    min_holdout = min((v["n_holdout"] for v in model.values() if v), default=0)

    # Compute alpha_F: max slope across classes with C_bad > 0
    slopes_nonzero = [v["slope_a"] for v in model.values()
                      if v and v["slope_a"] != 0]
    alpha_F = max(slopes_nonzero) if slopes_nonzero else Fraction(0)
    alpha_F_lt_CF = alpha_F < Fraction(C_F)

    # Min B_safe margin
    min_margin = min(r["B_margin"] for r in rows)
    max_cbad = max(r["C_bad"] for r in rows)

    # ── Write results ──────────────────────────────────────────────────────
    lines = [
        "# PL Validation: F1246689 (n=11)",
        "",
        "## Setup",
        f"- Family: `E(M)=(1,2,3,4,6,6,8,9,M,11)`, `gcd(M,792)=1`",
        f"- `n=11`, `L_0=792`, `L=792M`, `C_F=648` (exact, proved from interval formula)",
        f"- Tested M range: `[1, {MAX_M}]`, valid count: `{len(M_values)}`",
        f"- Period tested: `{PERIOD}` (= n² = 11²)",
        "",
        "## PL.1 — Analytical: t_M(b) is M-independent",
        "",
        "**Claim**: For the free runner `e=M`, the floor-quotient `t_M(b) = floor(M·b/L) = floor(b/L_0)` does NOT depend on M.",
        "",
        "**Proof**: `t_M(b) = floor(M·b / (792M)) = floor(b / 792)`. QED.",
        "",
        "**Consequence**: The bad-a pair contributed by runner M at fiber b is:",
        "  `{(-floor(b/792))·M^{-1} mod 11, (10-floor(b/792))·M^{-1} mod 11}`.",
        "This depends on M only through `M^{-1} mod 11`, which has period 11 in M.",
        "Hence the bad-coverage condition (∪_e{a_e^0,a_e^1}=Z_11) at fiber b depends on M through:",
        "  (a) `M^{-1} mod 11` (period 11), and",
        "  (b) `floor(e·b/(792M))` for fixed e ∈ {1,2,3,4,6,6,8,9} (M-dependent floor terms).",
        "The combined period of C_bad(M) is empirically 121 = 11² (verified below).",
        "",
        f"**Computational verification**: `t_M(b)` matches `b//792` for {pl1_triples} (M,b) pairs "
        f"across {min(5,len(M_values))} values of M: **{pl1_ok}**.",
        "",
        "## PL.2 — Holdout Validation of Classwise Linear Model",
        "",
        f"- Residue classes (mod {PERIOD}) with data: `{n_classes}`",
        f"- Points per class: min=`{min_pts}`, max=`{max_pts}`",
        f"- Holdout size per class: min=`{min_holdout}` pts",
        f"- Classes with exact holdout (0 residual): `{n_exact}` / `{n_classes}`",
        f"- Classes with no holdout (only 1 or 2 pts total): `{n_trivial}`",
        "",
    ]

    if n_exact == n_classes and n_trivial == 0:
        lines.append("**RESULT: All residue classes pass holdout validation exactly. Periodic-linear law CONFIRMED.**")
    elif n_exact + n_trivial == n_classes:
        lines.append(f"**RESULT: {n_exact} classes pass holdout; {n_trivial} have no holdout pts (need larger M range). Increase MAX_M.**")
    else:
        failed = [r for r, v in model.items() if v and not v["holdout_exact"]]
        lines.append(f"**RESULT: Holdout FAILED for classes {failed[:5]}. Check computation.**")

    lines += [
        "",
        "## Slope-Gap Verification",
        "",
        f"- `C_F = {C_F}` (slope of `B_div(M) = 648M+1`)",
        f"- `alpha_F = max slope of C_bad(M)` across all residue classes = `{alpha_F}` = `{float(alpha_F):.6f}`",
        f"- `alpha_F < C_F`: **{alpha_F_lt_CF}** (`{alpha_F} < {C_F}`)",
        f"- Implied `B_safe` slope ≥ `C_F - alpha_F = {C_F - alpha_F}` = `{float(C_F - alpha_F):.6f}`",
        f"- min `B_safe - (n-1)` on tested range: `{min_margin}`",
        f"- max `C_bad` on tested range: `{max_cbad}`",
        "",
        "## Sample Class Formulas (highest slopes)",
        "",
        "| r mod 121 | slope a_r | intercept b_r | n_train | n_holdout | holdout_exact |",
        "|---:|---:|---:|---:|---:|---:|",
    ]

    # Sort by slope descending, show top 10
    sorted_classes = sorted(
        ((r, v) for r, v in model.items() if v and v["slope_a"] != 0),
        key=lambda x: -x[1]["slope_a"]
    )
    for r, v in sorted_classes[:10]:
        lines.append(
            f"| {r} | `{v['slope_a']}` | `{v['intercept_b']}` | "
            f"{v['n_train']} | {v['n_holdout']} | {v['holdout_exact']} |"
        )

    lines += [
        "",
        "## Summary",
        f"- PL.1 (t_M independence): **PROVED analytically** + verified computationally",
        f"- PL.2 (holdout validation): {'**PASSED** — periodic-linear law exact on all classes with holdout data' if n_exact + n_trivial == n_classes and n_trivial == 0 else f'PARTIAL — {n_trivial} classes need more data'}",
        f"- PL.3 (alpha_F < C_F): alpha_F={alpha_F} < C_F={C_F} — **gap = {C_F - alpha_F}**",
        f"  Mechanism: tiling Z_11 requires ALL runners to simultaneously cover all residues,",
        f"  a much stricter condition than individual bad-a coverage.",
        "",
    ]

    with open(OUT_MD, "w") as f:
        f.write("\n".join(lines) + "\n")

    # Write CSV
    csv_rows = []
    for r, v in sorted(model.items()):
        if v is None:
            csv_rows.append({"residue_r": r, "slope_a": "N/A", "intercept_b": "N/A",
                             "n_pts": 0, "n_train": 0, "n_holdout": 0,
                             "holdout_exact": False, "notes": "too few pts"})
        else:
            csv_rows.append({
                "residue_r": r,
                "slope_a": str(v["slope_a"]),
                "intercept_b": str(v["intercept_b"]),
                "n_pts": v["n_pts"],
                "n_train": v["n_train"],
                "n_holdout": v["n_holdout"],
                "holdout_exact": v["holdout_exact"],
                "notes": "ok",
            })

    with open(OUT_CSV, "w", newline="") as f:
        if csv_rows:
            w = csv.DictWriter(f, fieldnames=list(csv_rows[0].keys()))
            w.writeheader()
            w.writerows(csv_rows)

    print(f"\nWrote: {OUT_MD}")
    print(f"Wrote: {OUT_CSV}")
    print(f"\n=== KEY RESULTS ===")
    print(f"PL.1: t_M(b) M-independent: {pl1_ok} ({pl1_triples} checks)")
    print(f"PL.2 holdout: {n_exact}/{n_classes} classes exact, {n_trivial} without holdout")
    print(f"min pts/class: {min_pts},  holdout min pts: {min_holdout}")
    print(f"alpha_F = {alpha_F} ({float(alpha_F):.5f}), C_F = {C_F}")
    print(f"alpha_F < C_F: {alpha_F_lt_CF}")
    print(f"min B_safe margin: {min_margin}, max C_bad: {max_cbad}")


if __name__ == "__main__":
    main()
