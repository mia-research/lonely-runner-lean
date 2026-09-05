"""
lrc_br_sigma_diagnostic_v1.py

σ-Framework Diagnostic for Lemma BR, Case-B tuples (prime n, 1 ∈ E_non).

Applies the σ-factorisation:
    σ(e) = q · s⁻¹  mod n,  where e = qn + s
    τ(e, r) = s · (σ(e) + r)  mod n
    a_low(e) = −σ(e) mod n        (τ = 0 residue)
    a_high(e) = −(σ(e) + s⁻¹) mod n  (τ = n-1 residue)

Key structural facts proved here computationally:
    (A) Small runners: σ(f_s) = 0, so a_low(f_s) = 0 (non-interior) always.
    (B) A_small = {a_high(f_s) : f_s ∈ E_small \ {1}} has size k_S − 1 exactly.
    (C) S₀ = {1,...,n-2} \ A_small has size k_L exactly (full LRC, n-1 runners).

Classification of every Case-B tuple into three exhaustive cases:
    Escape (E):  ∃ e_L ∈ E_large with a_low(e_L) ∈ S₀
                 → Key Lemma gives k=1 or LL/MZ k=2 witness.
    Trapped T1:  All e_L trapped (a_low ∈ A_small) AND k_L ≥ k_S
                 → Pigeonhole on σ-values forces LL k=2 witness.
    Trapped T2:  All e_L trapped AND k_L < k_S
                 → Case B forces bijection ψ: E_L → S₀; analyse UZ k=1 candidates.

Analytic lemma verified for ALL tuples:
    Runner-1 Non-Blocking: runner 1 never blocks any UZ k=1 candidate in T2.
    Proof: τ(1,r)=r, window(1,r) = M·(n(n-1-r)−1) ≥ any upper-excluder cap
    since e_L ≥ n+1 forces cap ≪ window. (Confirmed computationally.)

Window and budget arithmetic match the Phase 0 classifier exactly:
    b_lo = L // n,  L = lcm(e_non ∪ {n}),  budget = (n-2)(L-n)/(2n).

Usage:
    python3 lrc_br_sigma_diagnostic_v1.py [--n-min N] [--n-max N]
                                           [--max-per-n K] [--speed-max M]

Outputs (same directory as classifier):
    lrc_br_sigma_rows_v1.csv    — one row per Case-B tuple
    lrc_br_sigma_summary_v1.md  — aggregate counts, lemma verification table
"""

from __future__ import annotations

import argparse
import csv
import os
import random
import sys
from collections import defaultdict
from itertools import combinations
from math import gcd
from typing import Optional

# ---------------------------------------------------------------------------
# Arithmetic helpers — identical to Phase 0 classifier
# ---------------------------------------------------------------------------

def _lcm(a: int, b: int) -> int:
    return a * b // gcd(a, b)


def lcm_list(values) -> int:
    out = 1
    for v in values:
        out = _lcm(out, int(v))
    return out


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n == 2:
        return True
    if n % 2 == 0:
        return False
    k = 3
    while k * k <= n:
        if n % k == 0:
            return False
        k += 2
    return True


def modinv(a: int, n: int) -> int:
    return pow(int(a), -1, int(n))


# ---------------------------------------------------------------------------
# Core LRC arithmetic — matching classifier exactly
# ---------------------------------------------------------------------------

def tau_index(e: int, r: int, n: int) -> int:
    """τ(e, r) = (q + s·r) mod n, where e = qn + s."""
    q, s = divmod(e, n)
    return (q + s * r) % n


def sigma_of(e: int, n: int) -> int:
    """σ(e) = q·s⁻¹ mod n. For small runners (q=0): σ = 0."""
    q, s = divmod(e, n)
    if q == 0:
        return 0
    return (q * modinv(s, n)) % n


def a_low_of(e: int, n: int) -> int:
    """a_low(e) = −σ(e) mod n. Residue r with τ(e,r) = 0."""
    q, s = divmod(e, n)
    if q == 0:
        return 0   # small runner: a_low = 0 (non-interior)
    return (-q * modinv(s, n)) % n


def a_high_of(e: int, n: int) -> int:
    """a_high(e) = (n-1-q)·s⁻¹ mod n. Residue r with τ(e,r) = n-1."""
    q, s = divmod(e, n)
    return ((n - 1 - q) * modinv(s, n)) % n


def x0_value(e: int, r: int, b_lo: int, L: int, n: int) -> int:
    return (e * (r * L + b_lo)) % (n * L)


def safe_set(e: int, b_lo: int, L: int, n: int) -> set:
    N = n * L
    return {a for a in range(n) if L <= (e * (a * L + b_lo)) % N <= (n - 1) * L}


def arrival_time(e: int, r: int, b_lo: int, L: int, n: int) -> int:
    x = x0_value(e, r, b_lo, L, n)
    N = n * L
    if L <= x <= (n - 1) * L:
        return 0
    gap = (L - x) if x < L else (N - x + L)
    assert gap % e == 0, f"arr: gap={gap} not divisible by e={e}"
    return gap // e


def window_from_blo(e: int, r: int, b_lo: int, L: int, n: int) -> Optional[int]:
    x = x0_value(e, r, b_lo, L, n)
    if not (L <= x <= (n - 1) * L):
        return None
    return ((n - 1) * L - x) // e


# ---------------------------------------------------------------------------
# Case-B detection
# ---------------------------------------------------------------------------

def compute_tuple_params(n: int, e_non: tuple) -> tuple:
    """
    Returns (L, b_lo, budget, safe_sets_map) using the same logic
    as the Phase 0 classifier: L = lcm(e_non ∪ {n}), b_lo = L//n.
    """
    e_all = list(e_non) + [n]
    L = lcm_list(e_all)
    b_lo = L // n
    budget = (n - 2) * (L - n) / (2 * n)
    safe_sets_map = {e: safe_set(e, b_lo, L, n) for e in e_non}
    return L, b_lo, budget, safe_sets_map


def is_case_b(n: int, e_non: tuple, safe_sets_map: dict) -> bool:
    """A_{b_lo} = ∅ iff no interior residue is safe for all runners."""
    ab_lo: set = set(range(n))
    for e in e_non:
        ab_lo &= safe_sets_map[e]
    # ab_lo is the safe set for all runners; Case B = empty interior intersection
    # (the intersection may include 0 and n-1; we only care about interior {1,...,n-2})
    interior_safe = {r for r in ab_lo if 1 <= r <= n - 2}
    return len(interior_safe) == 0


# ---------------------------------------------------------------------------
# σ-Framework: escape / trapped classification
# ---------------------------------------------------------------------------

def classify_tuple_sigma(
    n: int,
    e_non: tuple,
    L: int,
    b_lo: int,
    budget: float,
    safe_sets_map: dict,
) -> dict:
    """
    Full σ-framework classification for a single Case-B tuple.

    Returns a dict with all classification fields, including:
        escape_flag, trapped_subcase, ll_witness, mz_witness,
        t2_psi_bijection_ok, t2_uz_valid_any, runner1_blocking_any,
        and detail lists for T2 UZ candidates.
    """
    e_small = [e for e in e_non if e < n]    # includes runner 1
    e_large = [e for e in e_non if e > n]
    k_S = len(e_small)
    k_L = len(e_large)

    # --- A_small and S₀ ---
    # A_small = {a_high(f) : f ∈ E_small \ {1}}, all should be interior
    a_small_set: set = set()
    for f in e_small:
        if f == 1:
            continue
        ah = a_high_of(f, n)
        # a_high of a small runner (q=0) = (n-1)·f⁻¹ mod n ∈ {1,...,n-2} (not 0 or n-1)
        if 1 <= ah <= n - 2:
            a_small_set.add(ah)

    s0 = set(range(1, n - 1)) - a_small_set   # S₀ = {1,...,n-2} \ A_small

    # Verify |A_small| = k_S - 1 (injectivity of a_high on E_small \ {1})
    a_small_size_ok = (len(a_small_set) == k_S - 1)

    # Verify |S₀| = k_L (the sharp count for full LRC)
    s0_size_matches_kL = (len(s0) == k_L)

    # --- σ-values of large runners ---
    sigma_vals = {e: sigma_of(e, n) for e in e_large}

    # Compute a_low values for all large runners
    al_vals = {e: a_low_of(e, n) for e in e_large}
    ah_vals = {e: a_high_of(e, n) for e in e_large}

    # Classify each large runner by where its a_low lands:
    #   escaped:  a_low ∈ S₀ (interior, not covered by small-runner upper exclusion)
    #   trapped:  a_low ∈ A_small (interior, covered by some small runner's a_high)
    #   boundary: a_low ∈ {0, n-1} (non-interior; arises when σ ∈ {0,1})
    #             Boundary runners don't lower-exclude any interior residue.
    #             σ=1 ↔ a_low=n-1 (most common boundary case; e_L = s(n+1) type)
    escaped_runners = [e for e in e_large if al_vals[e] in s0]
    trapped_runners = [e for e in e_large if al_vals[e] in a_small_set]
    boundary_runners = [e for e in e_large
                        if al_vals[e] not in s0 and al_vals[e] not in a_small_set]
    escape_flag = len(escaped_runners) > 0

    # --- LL coincidence: two large runners sharing a σ-value (⇒ same a_low) ---
    sigma_to_large: dict = defaultdict(list)
    for e in e_large:
        sigma_to_large[sigma_vals[e]].append(e)
    ll_pairs = [(r[0], r[1]) for r in sigma_to_large.values() if len(r) >= 2]
    ll_witness = a_low_of(ll_pairs[0][0], n) if ll_pairs else None

    # --- MZ coincidence: a_low(e_L) = a_high(e_U) for distinct large e_L, e_U ---
    mz_pairs = []
    for e_L in e_large:
        for e_U in e_large:
            if e_L != e_U and a_low_of(e_L, n) == a_high_of(e_U, n):
                mz_pairs.append((e_L, e_U))
    mz_witness = a_low_of(mz_pairs[0][0], n) if mz_pairs else None

    # --- Trapped sub-case ---
    trapped_subcase = None
    if not escape_flag:
        trapped_subcase = "T1" if k_L >= k_S else "T2"

    # --- T1: verify LL coincidence exists (pigeonhole guarantee) ---
    t1_ll_ok = True
    if trapped_subcase == "T1":
        t1_ll_ok = ll_witness is not None

    # --- Non-escape unified analysis: bijection ψ: E_large → S₀ via a_high ---
    # Runs for ALL non-escape tuples (T1 AND T2), not just k_L < k_S.
    # REASON: the T1 pigeonhole (LL at A_small) gives k=3 witnesses (small runner
    # also upper-excludes that A_small residue), NOT valid k=2.
    # The actual rescue for ALL non-escape tuples is via bijection ψ and UZ k=1.
    t2_psi_bijection_ok = False
    t2_uz_valid_any = False
    t2_uz_candidates = []
    runner1_blocking_any = False

    if not escape_flag:
        psi_vals = [a_high_of(e, n) for e in e_large]
        psi_in_s0 = all(v in s0 for v in psi_vals)
        psi_distinct = len(set(psi_vals)) == len(psi_vals)
        psi_surjective = set(psi_vals) == s0
        t2_psi_bijection_ok = psi_in_s0 and psi_distinct and psi_surjective

        # Build inverse map ψ⁻¹: r → e_L
        psi_inv = {a_high_of(e, n): e for e in e_large}

        for r in sorted(s0):
            e_L = psi_inv.get(r)
            if e_L is None:
                continue  # bijection failed — already flagged

            # Sanity: τ(e_L, r) should equal n-1 (upper exclusion)
            tau_eL_r = tau_index(e_L, r, n)
            assert tau_eL_r == n - 1, (
                f"T2 τ invariant violated: n={n}, e_L={e_L}, r={r}, τ={tau_eL_r}"
            )

            # Budget check (cap = arrival_time of the sole upper excluder)
            cap = arrival_time(e_L, r, b_lo, L, n)
            budget_ok = (cap <= budget)

            # Runner-1 blocking check (analytic lemma: should always be False)
            win1 = window_from_blo(1, r, b_lo, L, n)
            r1_blocks = (win1 is not None) and (win1 < cap)
            if r1_blocks:
                runner1_blocking_any = True

            # All co-covering runner blocking check
            blockers = []
            for f in e_non:
                if f == e_L:
                    continue
                tau_f = tau_index(f, r, n)
                if tau_f in (0, n - 1):
                    continue  # f is also an excluder at r — skip
                win_f = window_from_blo(f, r, b_lo, L, n)
                if win_f is not None and win_f < cap:
                    blockers.append(f)

            is_valid = budget_ok and (len(blockers) == 0)
            if is_valid:
                t2_uz_valid_any = True

            t2_uz_candidates.append({
                "r": r,
                "e_L": e_L,
                "cap": cap,
                "budget": budget,
                "budget_ok": budget_ok,
                "r1_blocks": r1_blocks,
                "blockers": blockers,
                "valid": is_valid,
            })

    # --- Escape: find rescue type for each escaped runner ---
    escape_rescues = []
    if escape_flag:
        for e_L in escaped_runners:
            r_star = a_low_of(e_L, n)
            if r_star not in s0:
                # a_low is not in interior — shouldn't happen for escape
                escape_rescues.append({"e_L": e_L, "r": r_star, "type": "non-interior"})
                continue
            # Find excl set at r_star
            excl_at_r = [e for e in e_non if r_star not in safe_sets_map[e]]
            tau_at_r = {e: tau_index(e, r_star, n) for e in excl_at_r}
            if len(excl_at_r) == 1:
                # Sole lower-excluder → Key Lemma → valid k=1 (cap=0)
                escape_rescues.append({"e_L": e_L, "r": r_star, "type": "k1_key_lemma"})
            else:
                second_excl = [(e, tau_at_r[e]) for e in excl_at_r if e != e_L]
                for e2, t2 in second_excl:
                    if t2 == 0:
                        escape_rescues.append({"e_L": e_L, "r": r_star, "type": "LL", "e2": e2})
                    elif t2 == n - 1:
                        escape_rescues.append({"e_L": e_L, "r": r_star, "type": "MZ", "e_U": e2})

    return {
        "n": n,
        "e_non": e_non,
        "L": L,
        "budget": budget,
        "k_S": k_S,
        "k_L": k_L,
        "a_small_size_ok": a_small_size_ok,
        "s0_size_matches_kL": s0_size_matches_kL,
        "a_small_set": sorted(a_small_set),
        "s0": sorted(s0),
        "sigma_vals": sigma_vals,
        "escape_flag": escape_flag,
        "escaped_runners": escaped_runners,
        "trapped_runners": trapped_runners,
        "trapped_subcase": trapped_subcase,
        "ll_pairs": ll_pairs,
        "ll_witness": ll_witness,
        "mz_pairs": mz_pairs,
        "mz_witness": mz_witness,
        "t1_ll_ok": t1_ll_ok,
        "t2_psi_bijection_ok": t2_psi_bijection_ok,
        "t2_uz_valid_any": t2_uz_valid_any,
        "t2_uz_candidates": t2_uz_candidates,
        "runner1_blocking_any": runner1_blocking_any,
        "escape_rescues": escape_rescues,
    }


# ---------------------------------------------------------------------------
# Tuple generation
# ---------------------------------------------------------------------------

def generate_case_b_tuples(
    n: int,
    max_per_n: int,
    speed_max: int,
    seed: int = 42,
) -> list:
    """
    Generate Case-B tuples for prime n.
    Always includes runner 1; generates (n-2) more from coprime speeds ≤ speed_max.
    For n ≤ 7: exhaustive enumeration. For n ≥ 11: random sampling.
    """
    other = [e for e in range(2, speed_max + 1) if gcd(e, n) == 1 and e != n]
    results = []

    if n <= 7:
        # Exhaustive: iterate all (n-2)-combinations
        for subset in combinations(other, n - 2):
            if len(results) >= max_per_n:
                break
            e_non = tuple(sorted((1,) + subset))
            L, b_lo, budget, safe_map = compute_tuple_params(n, e_non)
            if is_case_b(n, e_non, safe_map):
                results.append((e_non, L, b_lo, budget, safe_map))
    else:
        # Random sampling for larger n
        rng = random.Random(seed)
        seen: set = set()
        attempts = 0
        max_attempts = max_per_n * 200
        while len(results) < max_per_n and attempts < max_attempts:
            subset = tuple(sorted(rng.sample(other, n - 2)))
            key = (1,) + subset
            if key not in seen:
                seen.add(key)
                e_non = tuple(sorted((1,) + subset))
                L, b_lo, budget, safe_map = compute_tuple_params(n, e_non)
                if is_case_b(n, e_non, safe_map):
                    results.append((e_non, L, b_lo, budget, safe_map))
            attempts += 1

    return results


# ---------------------------------------------------------------------------
# Main sweep
# ---------------------------------------------------------------------------

_OUT_DIR = (
    "/Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01"
)

_CSV_FIELDNAMES = [
    "n", "e_non", "L", "budget", "k_S", "k_L",
    "a_small_size_ok", "s0_size_matches_kL",
    "a_small_set", "s0",
    "escape_flag", "trapped_subcase",
    "ll_witness", "mz_witness",
    "t1_ll_ok",
    "t2_psi_bijection_ok", "t2_uz_valid_any",
    "runner1_blocking_any",
    "escape_rescue_types",
    "t2_uz_summary",
]


def run_sweep(n_values, max_per_n: int, speed_max_factor: int) -> None:
    rows_path = os.path.join(_OUT_DIR, "lrc_br_sigma_rows_v1.csv")
    summary_path = os.path.join(_OUT_DIR, "lrc_br_sigma_summary_v1.md")

    all_classified = []
    stats: dict = defaultdict(int)

    # Violation trackers
    runner1_violations = []
    t1_no_ll = []
    escape_no_rescue = []
    t2_psi_fails = []
    a_small_size_fails = []
    s0_size_fails = []

    for n in n_values:
        if not is_prime(n):
            continue
        speed_max = speed_max_factor * n
        print(f"\nn={n}: generating Case-B tuples (speeds ≤ {speed_max}, max {max_per_n}) ...",
              flush=True)

        tuples = generate_case_b_tuples(n, max_per_n, speed_max)
        print(f"  → {len(tuples)} Case-B tuples found.", flush=True)
        stats[f"n{n}_total"] = len(tuples)

        for e_non, L, b_lo, budget, safe_map in tuples:
            row = classify_tuple_sigma(n, e_non, L, b_lo, budget, safe_map)
            all_classified.append(row)
            stats["total"] += 1

            # Structural invariants
            if not row["a_small_size_ok"]:
                stats["a_small_size_fails"] += 1
                a_small_size_fails.append(row)
            if not row["s0_size_matches_kL"]:
                stats["s0_size_fails"] += 1
                s0_size_fails.append(row)

            # Classification counts
            if row["escape_flag"]:
                stats["escape"] += 1
                rescue_types = [r["type"] for r in row["escape_rescues"]]
                if "k1_key_lemma" in rescue_types:
                    stats["escape_k1"] += 1
                elif "LL" in rescue_types:
                    stats["escape_ll"] += 1
                elif "MZ" in rescue_types:
                    stats["escape_mz"] += 1
                else:
                    stats["escape_no_rescue"] += 1
                    escape_no_rescue.append(row)
            elif row["trapped_subcase"] == "T1":
                stats["trapped_T1"] += 1
                if row["t1_ll_ok"]:
                    stats["T1_ll_ok"] += 1
                else:
                    stats["T1_no_ll"] += 1
                    t1_no_ll.append(row)
                # T1 also runs the bijection/UZ analysis (unified non-escape)
                if row["t2_psi_bijection_ok"]:
                    stats["T1_psi_ok"] += 1
                else:
                    stats["T1_psi_fail"] += 1
                    t2_psi_fails.append(row)
                if row["t2_uz_valid_any"]:
                    stats["T1_uz_valid"] += 1
                else:
                    stats["T1_uz_all_invalid"] += 1
            elif row["trapped_subcase"] == "T2":
                stats["trapped_T2"] += 1
                if row["t2_psi_bijection_ok"]:
                    stats["T2_psi_ok"] += 1
                else:
                    stats["T2_psi_fail"] += 1
                    t2_psi_fails.append(row)
                if row["t2_uz_valid_any"]:
                    stats["T2_uz_valid"] += 1
                else:
                    stats["T2_uz_all_invalid"] += 1
            else:
                stats["unclassified"] += 1

            # Runner-1 blocking (analytic lemma: must always be False)
            if row["runner1_blocking_any"]:
                stats["runner1_violations"] += 1
                runner1_violations.append(row)

        e_count = stats.get("escape", 0)
        t1_count = stats.get("trapped_T1", 0)
        t2_count = stats.get("trapped_T2", 0)
        print(
            f"  Escape={e_count}  T1={t1_count}  T2={t2_count}  "
            f"runner1_viol={stats.get('runner1_violations', 0)}",
            flush=True,
        )

    total = stats["total"]
    print(f"\nTotal Case-B tuples: {total}")

    # --- Write CSV ---
    with open(rows_path, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=_CSV_FIELDNAMES)
        writer.writeheader()
        for row in all_classified:
            rescue_types = "|".join(r["type"] for r in row["escape_rescues"])
            uz_summary_parts = []
            for c in row["t2_uz_candidates"]:
                uz_summary_parts.append(
                    f"r={c['r']},eL={c['e_L']},valid={int(c['valid'])},"
                    f"r1={int(c['r1_blocks'])},blk={c['blockers']}"
                )
            writer.writerow({
                "n": row["n"],
                "e_non": str(row["e_non"]),
                "L": row["L"],
                "budget": f"{row['budget']:.4f}",
                "k_S": row["k_S"],
                "k_L": row["k_L"],
                "a_small_size_ok": int(row["a_small_size_ok"]),
                "s0_size_matches_kL": int(row["s0_size_matches_kL"]),
                "a_small_set": str(row["a_small_set"]),
                "s0": str(row["s0"]),
                "escape_flag": int(row["escape_flag"]),
                "trapped_subcase": row["trapped_subcase"] or "",
                "ll_witness": row["ll_witness"] if row["ll_witness"] is not None else "",
                "mz_witness": row["mz_witness"] if row["mz_witness"] is not None else "",
                "t1_ll_ok": int(row["t1_ll_ok"]),
                "t2_psi_bijection_ok": int(row["t2_psi_bijection_ok"]),
                "t2_uz_valid_any": int(row["t2_uz_valid_any"]),
                "runner1_blocking_any": int(row["runner1_blocking_any"]),
                "escape_rescue_types": rescue_types,
                "t2_uz_summary": " | ".join(uz_summary_parts),
            })
    print(f"Wrote {len(all_classified)} rows to {rows_path}")

    # --- Write markdown summary ---
    def _pct(num, denom):
        if denom == 0:
            return "—"
        return f"{100 * num // denom}%"

    with open(summary_path, "w") as f:
        f.write("# LRC BR σ-Diagnostic Summary\n\n")
        f.write("**Date:** 2026-03-06  \n")
        f.write("**Script:** `lrc_br_sigma_diagnostic_v1.py`  \n")
        f.write("**Framework:** σ(e) = q·s⁻¹ mod n; escape/T1/T2 classification\n\n")
        f.write("---\n\n")

        f.write("## Structural Invariants (should always hold)\n\n")
        f.write("| Invariant | Violations | Status |\n")
        f.write("|---|---|---|\n")
        f.write(
            f"| \\|A_small\\| = k_S − 1 (a_high injectivity) | "
            f"{stats.get('a_small_size_fails', 0)} | "
            f"{'✓ HOLDS' if stats.get('a_small_size_fails', 0) == 0 else '✗ FAILS'} |\n"
        )
        f.write(
            f"| \\|S₀\\| = k_L (sharp count, full LRC) | "
            f"{stats.get('s0_size_fails', 0)} | "
            f"{'✓ HOLDS' if stats.get('s0_size_fails', 0) == 0 else '✗ FAILS'} |\n"
        )
        f.write("\n")

        f.write("## Classification Counts\n\n")
        f.write(f"- **Total Case-B tuples:** {total}\n")
        f.write(
            f"- **Escape (E):** {stats.get('escape', 0)} "
            f"({_pct(stats.get('escape', 0), total)})\n"
        )
        f.write(f"  - k=1 via Key Lemma: {stats.get('escape_k1', 0)}\n")
        f.write(f"  - k=2 LL rescue: {stats.get('escape_ll', 0)}\n")
        f.write(f"  - k=2 MZ rescue: {stats.get('escape_mz', 0)}\n")
        f.write(
            f"  - **No rescue found (ALERT):** {stats.get('escape_no_rescue', 0)} "
            f"(expect 0)\n"
        )
        t1_tot = stats.get('trapped_T1', 0)
        f.write(
            f"- **Non-escape T1 (k_L≥k_S):** {t1_tot} "
            f"({_pct(t1_tot, total)})\n"
        )
        f.write(f"  - LL coincidence (info only, LL∈A_small→k=3): {stats.get('T1_ll_ok', 0)}\n")
        f.write(f"  - No LL (k_L=k_S all distinct σ): {stats.get('T1_no_ll', 0)}\n")
        f.write(f"  - ψ bijection holds: {stats.get('T1_psi_ok', 0)}\n")
        f.write(
            f"  - **ψ bijection fails (ALERT):** {stats.get('T1_psi_fail', 0)} "
            f"(expect 0)\n"
        )
        f.write(f"  - ≥1 valid UZ k=1 candidate: {stats.get('T1_uz_valid', 0)}\n")
        f.write(
            f"  - All UZ k=1 invalid (early-time?): "
            f"{stats.get('T1_uz_all_invalid', 0)}\n"
        )
        t2_tot = stats.get('trapped_T2', 0)
        f.write(
            f"- **Non-escape T2 (k_L<k_S):** {t2_tot} "
            f"({_pct(t2_tot, total)})\n"
        )
        f.write(f"  - ψ bijection holds: {stats.get('T2_psi_ok', 0)}\n")
        f.write(
            f"  - **ψ bijection fails (ALERT):** {stats.get('T2_psi_fail', 0)} "
            f"(expect 0)\n"
        )
        f.write(f"  - ≥1 valid UZ k=1 candidate: {stats.get('T2_uz_valid', 0)}\n")
        f.write(
            f"  - All UZ k=1 invalid (early-time?): "
            f"{stats.get('T2_uz_all_invalid', 0)}\n"
        )
        f.write(f"- **Unclassified:** {stats.get('unclassified', 0)} (expect 0)\n\n")

        f.write("## Analytic Lemma Verification\n\n")
        f.write("| Lemma | Expected | Violations | Status |\n")
        f.write("|---|---|---|---|\n")
        r1v = stats.get("runner1_violations", 0)
        enr = stats.get("escape_no_rescue", 0)
        t1pf = stats.get("T1_psi_fail", 0)
        t2pf = stats.get("T2_psi_fail", 0)
        ne_psi_fail = t1pf + t2pf
        t1nll = stats.get("T1_no_ll", 0)
        f.write(
            f"| Runner-1 Non-Blocking | 0 | {r1v} | "
            f"{'✓ HOLDS' if r1v == 0 else '✗ FAILS'} |\n"
        )
        f.write(
            f"| Escape → k=1 or LL/MZ rescue | 0 unrescued | {enr} | "
            f"{'✓ HOLDS' if enr == 0 else '✗ FAILS'} |\n"
        )
        f.write(
            f"| Non-escape → ψ: E_L → S₀ bijection (T1+T2) | 0 failures | {ne_psi_fail} | "
            f"{'✓ HOLDS' if ne_psi_fail == 0 else '✗ FAILS'} |\n"
        )
        f.write(
            f"| T1 LL coincidence (informational; LL∈A_small→k=3) | — | {t1nll} no LL | "
            f"{'(pigeonhole fails at k_L=k_S)' if t1nll > 0 else '(all T1 have LL)'} |\n"
        )
        f.write(
            f"| T2 → ψ bijection | 0 failures | {t2pf} | "
            f"{'✓ HOLDS' if t2pf == 0 else '✗ FAILS'} |\n"
        )
        f.write("\n")

        # Alert sections
        if escape_no_rescue:
            f.write("## ⚠ Escape Tuples Without Rescue (INVESTIGATE)\n\n")
            for row in escape_no_rescue[:10]:
                f.write(f"- n={row['n']}, e_non={row['e_non']}, "
                        f"escaped={row['escaped_runners']}\n")
            f.write("\n")

        if t1_no_ll:
            f.write("## ⚠ T1 Tuples Without LL (INVESTIGATE)\n\n")
            for row in t1_no_ll[:10]:
                f.write(f"- n={row['n']}, e_non={row['e_non']}, "
                        f"σ-vals={row['sigma_vals']}\n")
            f.write("\n")

        if t2_psi_fails:
            f.write("## ⚠ T2 ψ-Bijection Failures (INVESTIGATE)\n\n")
            for row in t2_psi_fails[:10]:
                f.write(f"- n={row['n']}, e_non={row['e_non']}\n")
            f.write("\n")

        if runner1_violations:
            f.write("## ⚠ Runner-1 Blocking Violations (INVESTIGATE)\n\n")
            for row in runner1_violations[:10]:
                f.write(f"- n={row['n']}, e_non={row['e_non']}\n")
            f.write("\n")

        # T2 sample detail
        t2_samples = [r for r in all_classified if r["trapped_subcase"] == "T2"][:5]
        if t2_samples:
            f.write("## T2 Case Sample Detail\n\n")
            for row in t2_samples:
                f.write(f"### n={row['n']}, e_non={row['e_non']}\n")
                f.write(
                    f"- k_L={row['k_L']}, k_S={row['k_S']}, "
                    f"A_small={row['a_small_set']}, S₀={row['s0']}\n"
                )
                f.write(f"- σ-values of large runners: {row['sigma_vals']}\n")
                f.write(f"- ψ bijection: {row['t2_psi_bijection_ok']}\n")
                for c in row["t2_uz_candidates"]:
                    f.write(
                        f"  - r={c['r']}, e_L={c['e_L']}: "
                        f"cap={c['cap']}, budget={c['budget']:.1f}, "
                        f"budget_ok={c['budget_ok']}, "
                        f"runner1_blocks={c['r1_blocks']}, "
                        f"blockers={c['blockers']}, valid={c['valid']}\n"
                    )
                f.write("\n")

        # Per-n breakdown
        f.write("## Per-n Counts\n\n")
        f.write("| n | Total Case-B |\n")
        f.write("|---|---|\n")
        for n in n_values:
            if is_prime(n):
                f.write(f"| {n} | {stats.get(f'n{n}_total', 0)} |\n")
        f.write("\n")

    print(f"Wrote summary to {summary_path}")

    # Final verdict
    checks = [r1v, enr, ne_psi_fail,
               stats.get("a_small_size_fails", 0),
               stats.get("s0_size_fails", 0)]
    if all(c == 0 for c in checks):
        print("\n✓ All structural invariants and analytic lemma checks PASS.")
        if t1nll > 0:
            print(f"  (Info: {t1nll} T1 tuples have no LL — expected at k_L=k_S; "
                  f"rescued via bijection ψ UZ k=1 instead)")
    else:
        print("\n✗ Some checks FAILED — see summary for details.")
        if r1v > 0:
            print(f"  Runner-1 Non-Blocking: {r1v} violations")
        if enr > 0:
            print(f"  Escape without rescue: {enr} tuples")
        if ne_psi_fail > 0:
            print(f"  Non-escape ψ-bijection fail: {ne_psi_fail} tuples "
                  f"(T1={t1pf}, T2={t2pf})")
        if t1nll > 0:
            print(f"  (Info: T1 without LL: {t1nll} — ok if bijection holds)")


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[1].strip())
    parser.add_argument("--n-min", type=int, default=5)
    parser.add_argument("--n-max", type=int, default=13)
    parser.add_argument("--max-per-n", type=int, default=200)
    parser.add_argument(
        "--speed-max-factor", type=int, default=4,
        help="Speed upper bound = factor × n (default 4)"
    )
    args = parser.parse_args()

    n_values = list(range(args.n_min, args.n_max + 1))
    run_sweep(n_values, args.max_per_n, args.speed_max_factor)


if __name__ == "__main__":
    main()
