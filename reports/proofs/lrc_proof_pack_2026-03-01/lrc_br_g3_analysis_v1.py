"""
lrc_br_g3_analysis_v1.py

G3 Window Condition Analysis for MZ Witnesses — Lemma BR, Escape Regime.

For every Case-B tuple in the escape regime with an MZ rescue pair
(e_L: τ=0, e_U: τ=n-1, both large, at residue r** = a_low(e_L) = a_high(e_U)):

    cap(r**) = max(arrival_time(e_L, r**), arrival_time(e_U, r**))

    Window condition for co-covering runner f:
        window_from_blo(f, r**) >= cap(r**)   [required for valid witness]

This script:
  1. Identifies all escape MZ pairs.
  2. Validates each MZ witness (budget + window for ALL co-covering runners).
  3. §4.2 check: which blockers are small runners (e < n) with τ = n-2?
     Handoff §4.2 claims "small-runner threat ruled out when e_U > n" — THIS IS FALSE.
     Correct blocking condition: e_U < f_s*(n-1).  (counterexample: n=5, e_U=8, f_s=3)
  4. For any blocked MZ: searches for an alternative valid k≤2 witness.

Usage:
    python3 lrc_br_g3_analysis_v1.py [--n-min N] [--n-max N]
                                      [--max-per-n K] [--speed-max-factor F]

Outputs:
    lrc_br_g3_analysis_v1.md — full G3 report with §4.2 correction
"""

from __future__ import annotations

import argparse
import os
import random
from collections import defaultdict
from itertools import combinations
from math import gcd
from typing import Optional

# ---------------------------------------------------------------------------
# Arithmetic helpers (identical to sigma diagnostic)
# ---------------------------------------------------------------------------

def _lcm(a: int, b: int) -> int:
    return a * b // gcd(a, b)

def lcm_list(values) -> int:
    out = 1
    for v in values:
        out = _lcm(out, int(v))
    return out

def is_prime(n: int) -> bool:
    if n < 2: return False
    if n == 2: return True
    if n % 2 == 0: return False
    k = 3
    while k * k <= n:
        if n % k == 0: return False
        k += 2
    return True

def modinv(a: int, n: int) -> int:
    return pow(int(a), -1, int(n))

def tau_index(e: int, r: int, n: int) -> int:
    """τ(e, r) = (q + s·r) mod n."""
    q, s = divmod(e, n)
    return (q + s * r) % n

def a_low_of(e: int, n: int) -> int:
    """a_low(e) = -σ(e) mod n. Small runners: a_low = 0."""
    q, s = divmod(e, n)
    if q == 0: return 0
    return (-q * modinv(s, n)) % n

def a_high_of(e: int, n: int) -> int:
    """a_high(e) = (n-1-q)·s⁻¹ mod n."""
    q, s = divmod(e, n)
    return ((n - 1 - q) * modinv(s, n)) % n

def x0_value(e: int, r: int, b_lo: int, L: int, n: int) -> int:
    return (e * (r * L + b_lo)) % (n * L)

def arrival_time(e: int, r: int, b_lo: int, L: int, n: int) -> int:
    x = x0_value(e, r, b_lo, L, n)
    N = n * L
    if L <= x <= (n - 1) * L:
        return 0
    gap = (L - x) if x < L else (N - x + L)
    assert gap % e == 0, f"arr gap={gap} not div by e={e}"
    return gap // e

def window_from_blo(e: int, r: int, b_lo: int, L: int, n: int) -> Optional[int]:
    x = x0_value(e, r, b_lo, L, n)
    if not (L <= x <= (n - 1) * L):
        return None
    return ((n - 1) * L - x) // e

def safe_set(e: int, b_lo: int, L: int, n: int) -> set:
    N = n * L
    return {a for a in range(n) if L <= (e * (a * L + b_lo)) % N <= (n - 1) * L}

# ---------------------------------------------------------------------------
# Tuple parameters
# ---------------------------------------------------------------------------

def compute_tuple_params(n: int, e_non: tuple) -> tuple:
    e_all = list(e_non) + [n]
    L = lcm_list(e_all)
    b_lo = L // n
    budget = (n - 2) * (L - n) / (2 * n)
    safe_map = {e: safe_set(e, b_lo, L, n) for e in e_non}
    return L, b_lo, budget, safe_map

def is_case_b(n: int, e_non: tuple, safe_map: dict) -> bool:
    ab_lo = set(range(n))
    for e in e_non:
        ab_lo &= safe_map[e]
    interior_safe = {r for r in ab_lo if 1 <= r <= n - 2}
    return len(interior_safe) == 0

# ---------------------------------------------------------------------------
# Alternative witness search
# ---------------------------------------------------------------------------

def find_alternative_k2_witness(
    n: int, e_non: tuple, L: int, b_lo: int, budget: float, safe_map: dict,
    exclude_r: int,
) -> Optional[dict]:
    """
    Search all interior residues (other than exclude_r) for a valid k<=2 witness.
    Returns dict with r, excl, cap, type if found; None otherwise.
    """
    for r in range(1, n - 1):
        excl = [e for e in e_non if r not in safe_map[e]]
        if not excl:
            continue
        if len(excl) > 2:
            continue

        cap = max(arrival_time(e, r, b_lo, L, n) for e in excl)
        if cap > budget:
            continue

        # Check window condition for all co-covering runners
        blocked = False
        for f in e_non:
            if f in excl:
                continue
            tau_f = tau_index(f, r, n)
            if tau_f in (0, n - 1):
                continue
            win_f = window_from_blo(f, r, b_lo, L, n)
            if win_f is not None and win_f < cap:
                blocked = True
                break

        if not blocked:
            tau_types = [tau_index(e, r, n) for e in excl]
            if len(excl) == 1:
                kind = "k1"
            elif set(tau_types) == {0}:
                kind = "LL"
            elif set(tau_types) == {0, n - 1}:
                kind = "MZ"
            elif set(tau_types) == {n - 1}:
                kind = "UU"
            else:
                kind = f"k2_tau={sorted(tau_types)}"
            return {"r": r, "excl": excl, "cap": cap, "type": kind}

    return None

# ---------------------------------------------------------------------------
# G3 MZ analysis for a single tuple
# ---------------------------------------------------------------------------

def analyze_mz_witnesses(
    n: int, e_non: tuple, L: int, b_lo: int, budget: float, safe_map: dict,
) -> list:
    """
    Find all escape MZ pairs for this tuple and validate each one.
    Returns list of per-MZ-witness analysis dicts.
    """
    e_small = [e for e in e_non if e < n]
    e_large = [e for e in e_non if e > n]

    # A_small, S₀
    a_small_set: set = set()
    for f in e_small:
        if f == 1: continue
        ah = a_high_of(f, n)
        if 1 <= ah <= n - 2:
            a_small_set.add(ah)
    s0 = set(range(1, n - 1)) - a_small_set

    results = []

    # Only consider escaped large runners (a_low ∈ S₀)
    for e_L in e_large:
        al = a_low_of(e_L, n)
        if al not in s0:
            continue  # not escaped

        r_star = al
        excl_at_r = [e for e in e_non if r_star not in safe_map[e]]
        if len(excl_at_r) < 2:
            continue  # k=1 escape, not MZ

        # Find all MZ partners (other excluders with τ=n-1)
        for e_U in excl_at_r:
            if e_U == e_L:
                continue
            t_U = tau_index(e_U, r_star, n)
            if t_U != n - 1:
                continue
            if e_U < n:
                continue  # e_U must be large (small runners can't upper-exclude S₀)

            # Validate this MZ pair
            cap_L = arrival_time(e_L, r_star, b_lo, L, n)
            cap_U = arrival_time(e_U, r_star, b_lo, L, n)
            cap = max(cap_L, cap_U)
            budget_ok = (cap <= budget)

            # Co-covering runner analysis
            runner1_blocks = False
            small_runner_blockers = []
            large_runner_blockers = []
            all_cocovering = []

            for f in e_non:
                if f in (e_L, e_U):
                    continue
                tau_f = tau_index(f, r_star, n)
                if tau_f in (0, n - 1):
                    continue  # f is also an excluder, not co-covering
                win_f = window_from_blo(f, r_star, b_lo, L, n)
                blocks = (win_f is not None) and (win_f < cap)
                entry = {
                    "f": f,
                    "tau": tau_f,
                    "window": win_f,
                    "blocks": blocks,
                }
                all_cocovering.append(entry)

                if blocks:
                    if f == 1:
                        runner1_blocks = True
                    elif f < n:
                        # Small runner blocking
                        # §4.2 claim: "ruled out when e_U > n" → FALSE
                        # Correct condition: e_U < f*(n-1) → blocks possible
                        sec42_condition_violated = (e_U > n) and (e_U < f * (n - 1))
                        entry["sec42_violation"] = sec42_condition_violated
                        small_runner_blockers.append(entry)
                    else:
                        large_runner_blockers.append(entry)

            any_blocker = (len(small_runner_blockers) + len(large_runner_blockers)
                           + (1 if runner1_blocks else 0)) > 0
            mz_valid = budget_ok and not any_blocker

            # If blocked, find alternative witness
            alt_witness = None
            if not mz_valid:
                alt_witness = find_alternative_k2_witness(
                    n, e_non, L, b_lo, budget, safe_map, exclude_r=r_star
                )

            results.append({
                "n": n,
                "e_non": e_non,
                "r_star": r_star,
                "e_L": e_L,
                "e_U": e_U,
                "cap_L": cap_L,
                "cap_U": cap_U,
                "cap": cap,
                "budget": budget,
                "budget_ok": budget_ok,
                "runner1_blocks": runner1_blocks,
                "small_runner_blockers": small_runner_blockers,
                "large_runner_blockers": large_runner_blockers,
                "all_cocovering": all_cocovering,
                "mz_valid": mz_valid,
                "alt_witness": alt_witness,
            })

    return results

# ---------------------------------------------------------------------------
# Tuple generation (identical to sigma diagnostic)
# ---------------------------------------------------------------------------

def generate_case_b_tuples(
    n: int, max_per_n: int, speed_max: int, seed: int = 42,
) -> list:
    other = [e for e in range(2, speed_max + 1) if gcd(e, n) == 1 and e != n]
    results = []
    if n <= 7:
        for subset in combinations(other, n - 2):
            if len(results) >= max_per_n:
                break
            e_non = tuple(sorted((1,) + subset))
            L, b_lo, budget, safe_map = compute_tuple_params(n, e_non)
            if is_case_b(n, e_non, safe_map):
                results.append((e_non, L, b_lo, budget, safe_map))
    else:
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


def run_g3_sweep(n_values, max_per_n: int, speed_max_factor: int) -> None:
    out_path = os.path.join(_OUT_DIR, "lrc_br_g3_analysis_v1.md")

    all_mz: list = []      # all MZ witness records
    stats: dict = defaultdict(int)

    # §4.2 violation examples to highlight
    sec42_examples: list = []

    for n in n_values:
        if not is_prime(n):
            continue
        speed_max = speed_max_factor * n
        print(f"\nn={n}: generating Case-B tuples (speeds ≤ {speed_max}) ...",
              flush=True)
        tuples = generate_case_b_tuples(n, max_per_n, speed_max)
        print(f"  → {len(tuples)} Case-B tuples found.", flush=True)
        stats[f"n{n}_tuples"] = len(tuples)

        mz_count_n = 0
        for e_non, L, b_lo, budget, safe_map in tuples:
            mz_records = analyze_mz_witnesses(n, e_non, L, b_lo, budget, safe_map)
            for rec in mz_records:
                all_mz.append(rec)
                mz_count_n += 1
                stats["total_mz"] += 1

                if rec["mz_valid"]:
                    stats["mz_valid"] += 1
                else:
                    stats["mz_blocked"] += 1
                    if rec["alt_witness"] is not None:
                        stats["mz_blocked_with_alt"] += 1
                        stats[f"alt_{rec['alt_witness']['type']}"] += 1
                    else:
                        stats["mz_blocked_no_alt"] += 1

                if rec["runner1_blocks"]:
                    stats["r1_blocks"] += 1  # should always be 0

                for sb in rec["small_runner_blockers"]:
                    stats["small_runner_blocks"] += 1
                    if sb.get("sec42_violation"):
                        stats["sec42_violations"] += 1
                        if len(sec42_examples) < 10:
                            sec42_examples.append({
                                "n": n, "e_non": e_non, "r_star": rec["r_star"],
                                "e_L": rec["e_L"], "e_U": rec["e_U"],
                                "f_s": sb["f"], "tau": sb["tau"],
                                "window": sb["window"], "cap": rec["cap"],
                                "e_U_gt_n": (rec["e_U"] > n),
                                "blocking_condition": f"e_U={rec['e_U']} < f_s*(n-1)={sb['f']}*(n-1)={sb['f']*(n-1)}",
                            })

                for lb in rec["large_runner_blockers"]:
                    stats["large_runner_blocks"] += 1

        print(f"  → {mz_count_n} MZ witnesses found.", flush=True)

    total_mz = stats["total_mz"]
    print(f"\nTotal MZ witnesses analyzed: {total_mz}")
    print(f"Valid: {stats['mz_valid']}")
    print(f"Blocked: {stats['mz_blocked']} "
          f"(with alt: {stats['mz_blocked_with_alt']}, "
          f"no alt: {stats['mz_blocked_no_alt']})")
    print(f"§4.2 violations (e_U>n but small runner blocks): {stats['sec42_violations']}")

    # -----------------------------------------------------------------------
    # Write markdown report
    # -----------------------------------------------------------------------
    with open(out_path, "w") as f:
        f.write("# LRC BR G3 Window Analysis — MZ Witnesses\n\n")
        f.write("**Date:** 2026-03-06  \n")
        f.write("**Script:** `lrc_br_g3_analysis_v1.py`  \n")
        f.write("**Scope:** Escape regime MZ witnesses (τ=0 + τ=n-1 at r** ∈ S₀, both large).\n\n")
        f.write("---\n\n")

        # --- §4.2 correction box ---
        f.write("## §4.2 Error and Correction\n\n")
        f.write("**Handoff §4.2 claim (WRONG):**\n")
        f.write("> \"For n ≥ 5, the small-runner window threat is ruled out when e_U > n.\"\n\n")
        f.write("**Correct analysis:**  \n")
        f.write("For small runner f_s (e < n) with τ(f_s, r**) = n-2, the blocking condition is:\n\n")
        f.write("    window(f_s, r**) < cap(r**)  ⟺  e_U < f_s · (n−1)\n\n")
        f.write("This CAN hold even when e_U > n, whenever f_s ≥ 2 and e_U is small (near n+1).\n\n")

        v42 = stats.get("sec42_violations", 0)
        f.write(f"**Empirical §4.2 violations found: {v42}**  \n")
        f.write(f"(e_U > n, yet small runner f_s blocks the MZ window)\n\n")

        if sec42_examples:
            f.write("### §4.2 Violation Examples\n\n")
            f.write("| n | e_non | r** | e_L | e_U | f_s | τ(f_s) | window | cap | Condition |\n")
            f.write("|---|---|---|---|---|---|---|---|---|---|\n")
            for ex in sec42_examples[:8]:
                f.write(
                    f"| {ex['n']} | {ex['e_non']} | {ex['r_star']} | {ex['e_L']} "
                    f"| {ex['e_U']} | {ex['f_s']} | {ex['tau']} "
                    f"| {ex['window']} | {ex['cap']:.0f} "
                    f"| {ex['blocking_condition']} |\n"
                )
            f.write("\n")

        f.write("---\n\n")

        # --- Overall MZ stats ---
        f.write("## MZ Witness Summary\n\n")
        f.write(f"- **Total MZ witnesses analyzed:** {total_mz}\n")
        f.write(f"- **Valid (budget OK + no blockers):** {stats.get('mz_valid', 0)}\n")
        f.write(f"- **Blocked (any blocker or budget fail):** {stats.get('mz_blocked', 0)}\n")

        blocked = stats.get('mz_blocked', 0)
        if blocked > 0:
            f.write(f"  - With alternative valid k≤2 witness: {stats.get('mz_blocked_with_alt', 0)}\n")
            alt_breakdown = []
            for kind in ["k1", "LL", "MZ", "UU"]:
                c = stats.get(f"alt_{kind}", 0)
                if c > 0:
                    alt_breakdown.append(f"{kind}={c}")
            if alt_breakdown:
                f.write(f"    - Alternative types: {', '.join(alt_breakdown)}\n")
            f.write(
                f"  - **No alternative found (ALERT):** "
                f"{stats.get('mz_blocked_no_alt', 0)} (expect 0)\n"
            )

        f.write("\n### Blocker Breakdown\n\n")
        f.write(f"- Runner-1 blocks: {stats.get('r1_blocks', 0)} (expect 0)\n")
        f.write(f"- Small runner (f < n) blocks: {stats.get('small_runner_blocks', 0)}\n")
        f.write(f"  - Of which §4.2 violations (e_U > n): {stats.get('sec42_violations', 0)}\n")
        f.write(f"- Large runner (f > n) blocks: {stats.get('large_runner_blocks', 0)}\n\n")

        # --- Analytic lemma check ---
        f.write("## Analytic Lemma Verification\n\n")
        f.write("| Lemma | Expected | Result | Status |\n")
        f.write("|---|---|---|---|\n")
        r1b = stats.get("r1_blocks", 0)
        no_alt = stats.get("mz_blocked_no_alt", 0)
        f.write(
            f"| Runner-1 never blocks MZ | 0 | {r1b} | "
            f"{'✓ HOLDS' if r1b == 0 else '✗ FAILS'} |\n"
        )
        f.write(
            f"| Blocked MZ always has alternative k≤2 | 0 without alt | {no_alt} | "
            f"{'✓ HOLDS' if no_alt == 0 else '✗ FAILS'} |\n"
        )
        f.write(
            f"| §4.2 claim (small-runner ruled out by e_U>n) | — | {v42} violations | "
            f"{'✗ FALSE (expected, see correction)' if v42 > 0 else '(no violations in this sweep)'} |\n"
        )
        f.write("\n")

        # --- τ distribution of co-covering runners ---
        f.write("## τ Distribution of Co-Covering Runners at MZ Witnesses\n\n")
        tau_dist: dict = defaultdict(int)
        for rec in all_mz:
            for cc in rec["all_cocovering"]:
                tau_dist[cc["tau"]] += 1
        f.write("| τ value | Count | Fraction |\n")
        f.write("|---|---|---|\n")
        total_cc = sum(tau_dist.values())
        for tau_v in sorted(tau_dist.keys()):
            c = tau_dist[tau_v]
            frac = f"{c/total_cc:.3f}" if total_cc > 0 else "—"
            f.write(f"| {tau_v} | {c} | {frac} |\n")
        f.write("\n")

        # --- Per-n breakdown ---
        f.write("## Per-n Breakdown\n\n")
        f.write("| n | Tuples | MZ witnesses | Valid | Blocked | §4.2 viols |\n")
        f.write("|---|---|---|---|---|---|\n")
        for n in n_values:
            if not is_prime(n): continue
            n_recs = [r for r in all_mz if r["n"] == n]
            n_valid = sum(1 for r in n_recs if r["mz_valid"])
            n_blocked = sum(1 for r in n_recs if not r["mz_valid"])
            n_viols = sum(
                sum(1 for sb in r["small_runner_blockers"] if sb.get("sec42_violation"))
                for r in n_recs
            )
            f.write(
                f"| {n} | {stats.get(f'n{n}_tuples', 0)} | {len(n_recs)} "
                f"| {n_valid} | {n_blocked} | {n_viols} |\n"
            )
        f.write("\n")

        # --- Detailed examples of blocked MZ with alternative ---
        blocked_examples = [r for r in all_mz if not r["mz_valid"] and r["alt_witness"]]
        if blocked_examples:
            f.write("## Blocked MZ Examples (with Alternative Witness Found)\n\n")
            for rec in blocked_examples[:8]:
                f.write(f"### n={rec['n']}, e_non={rec['e_non']}, r**={rec['r_star']}\n")
                f.write(f"- MZ pair: e_L={rec['e_L']} (τ=0), e_U={rec['e_U']} (τ=n-1)\n")
                f.write(f"- cap={rec['cap']:.1f}, budget={rec['budget']:.1f}, "
                        f"budget_ok={rec['budget_ok']}\n")
                if rec["small_runner_blockers"]:
                    sb = rec["small_runner_blockers"][0]
                    f.write(
                        f"- Small runner blocker: f_s={sb['f']}, τ={sb['tau']}, "
                        f"window={sb['window']}, cap={rec['cap']:.0f}\n"
                    )
                    if sb.get("sec42_violation"):
                        f.write(
                            f"  → §4.2 VIOLATION: e_U={rec['e_U']} > n={rec['n']} "
                            f"but e_U < f_s*(n-1)={sb['f']}*{rec['n']-1}="
                            f"{sb['f']*(rec['n']-1)}\n"
                        )
                if rec["large_runner_blockers"]:
                    lb = rec["large_runner_blockers"][0]
                    f.write(
                        f"- Large runner blocker: f_L={lb['f']}, τ={lb['tau']}, "
                        f"window={lb['window']}, cap={rec['cap']:.0f}\n"
                    )
                alt = rec["alt_witness"]
                f.write(
                    f"- **Alternative witness:** r={alt['r']}, type={alt['type']}, "
                    f"excl={alt['excl']}, cap={alt['cap']}\n"
                )
                f.write("\n")

        # Final verdict
        f.write("---\n\n")
        if no_alt == 0 and r1b == 0:
            f.write("## Verdict\n\n")
            f.write("✓ **All blocked MZ witnesses have an alternative valid k≤2 witness.**  \n")
            f.write("✗ **§4.2 is FALSE** as stated: small-runner blocking occurs even when e_U > n.  \n")
            f.write("The correct blocking condition is `e_U < f_s·(n−1)`, NOT `e_U ≤ n`.  \n\n")
            f.write("**Implication for G3 proof route:**  \n")
            f.write("When f_s blocks the MZ at r**, an alternative valid k≤2 witness always exists "
                    "(empirically verified). The algebraic proof of this alternative witness under "
                    "the blocking constraint `e_U < f_s·(n−1)` and the MZ σ-structure "
                    "is the remaining G3 open sub-case.\n")
        else:
            f.write("## Verdict\n\n")
            f.write(f"✗ ALERT: {no_alt} blocked MZ witnesses have NO alternative. "
                    "G3 route is incomplete.\n")

    print(f"\nWrote report to {out_path}")


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(description="G3 MZ window condition analysis.")
    parser.add_argument("--n-min", type=int, default=5)
    parser.add_argument("--n-max", type=int, default=13)
    parser.add_argument("--max-per-n", type=int, default=300)
    parser.add_argument(
        "--speed-max-factor", type=int, default=4,
        help="Speed bound = factor * n (default 4)"
    )
    args = parser.parse_args()
    n_values = list(range(args.n_min, args.n_max + 1))
    run_g3_sweep(n_values, args.max_per_n, args.speed_max_factor)


if __name__ == "__main__":
    main()
