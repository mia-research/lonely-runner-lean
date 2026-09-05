"""
lrc_br_witness_classifier_v1.py

Phase 0 classifier for the Lemma BR low-multiplicity witness route.

For each Case-B tuple in the sweep, enumerates ALL residues r in Z_n and
classifies each by exclusion multiplicity k = |Excl(r)|, computing:

  - excl_set: runners excluding r at b_lo
  - cap: max arr(e, r) over excl_set
  - budget_ok: cap <= budget
  - For each co-covering runner: full c_e, full strip {n-c_e,...,n-2},
    tau, window_from_blo, whether it blocks (window < cap)
  - valid: budget_ok AND no blockers
  - cascade_info: for each blocker e', its a_high and a_low as natural
    successor candidates (not claimed to be valid — just mapped)

The strip computation uses the FULL c_e formula:
  c_e = ceil((e * A_zone + e* * s_e) / (n * e*))
where e* is the dominant excluder (max arrival). Strip size = c_e - 1,
which can be 2 for small runners with e >= ~2n/3 (c_e = 3).

Residues with |Excl| > 3 are recorded but not deeply analyzed.

Outputs:
  lrc_br_witness_classifier_rows_v1.csv   — one row per (tuple, residue)
  lrc_br_witness_classifier_summary_v1.md — per-n counts + hypothesis status

Decision gate: if any Case-B tuple has no valid k<=2 witness, the
low-multiplicity-2 hypothesis is falsified and the G4BI roadmap pivot activates.
"""

from __future__ import annotations

import argparse
import csv
import os
from itertools import combinations
from math import gcd
from typing import Sequence


# ---------------------------------------------------------------------------
# Arithmetic helpers (same as existing harness)
# ---------------------------------------------------------------------------

def lcm(a: int, b: int) -> int:
    return a * b // gcd(a, b)


def lcm_list(values: Sequence[int]) -> int:
    out = 1
    for v in values:
        out = lcm(out, v)
    return out


def gcd_list(values: Sequence[int]) -> int:
    out = values[0]
    for v in values[1:]:
        out = gcd(out, v)
    return out


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    k = 3
    while k * k <= n:
        if n % k == 0:
            return False
        k += 2
    return True


def ceil_div(a: int, b: int) -> int:
    return -(-a // b)


# ---------------------------------------------------------------------------
# LRC arithmetic (matching harness exactly)
# ---------------------------------------------------------------------------

def safe_set(e: int, b: int, L: int, n: int) -> set[int]:
    N = n * L
    return {
        a
        for a in range(n)
        if L <= (e * (a * L + b)) % N <= (n - 1) * L
    }


def x0_value(e: int, r: int, b_lo: int, L: int, n: int) -> int:
    return (e * (r * L + b_lo)) % (n * L)


def tau_index(e: int, r: int, n: int) -> int:
    q, s = divmod(e, n)
    return (q + s * r) % n


def zone_at_blo(e: int, r: int, n: int) -> str:
    tau = tau_index(e, r, n)
    if tau == 0:
        return "lower"
    if tau == n - 1:
        return "upper"
    return "safe"


def arrival_time(e: int, r: int, b_lo: int, L: int, n: int) -> int:
    x = x0_value(e, r, b_lo, L, n)
    N = n * L
    if L <= x <= (n - 1) * L:
        return 0
    gap = (L - x) if x < L else (N - x + L)
    assert gap % e == 0, f"arr: gap={gap} not divisible by e={e} (n={n} r={r})"
    return gap // e


def window_from_blo(e: int, r: int, b_lo: int, L: int, n: int) -> int | None:
    x = x0_value(e, r, b_lo, L, n)
    if not (L <= x <= (n - 1) * L):
        return None
    return ((n - 1) * L - x) // e


def zone_arrival_numerator(e_star: int, zone: str, n: int) -> int:
    _, s_star = divmod(e_star, n)
    if zone == "lower":
        return n - s_star
    if zone == "upper":
        return 2 * n - s_star
    raise ValueError(f"unexpected zone: {zone!r}")


def strip_threshold(e: int, e_star: int, zone_num: int, n: int) -> int:
    """c_e = ceil((e * zone_num + e* * s_e) / (n * e*))"""
    _, s = divmod(e, n)
    return ceil_div(e * zone_num + e_star * s, n * e_star)


def forbidden_tau_strip(
    e: int, e_star: int, zone_num: int, n: int
) -> tuple[int, int] | None:
    """Full forbidden tau strip {n-c_e, ..., n-2}. None if c_e <= 1."""
    c_e = strip_threshold(e, e_star, zone_num, n)
    if c_e <= 1:
        return None
    start = n - c_e
    end = n - 2
    if start > end:
        return None
    return start, end


# ---------------------------------------------------------------------------
# Cascade helpers: natural successor residues for each runner
# ---------------------------------------------------------------------------

def a_low_of(e: int, n: int) -> int:
    """Residue r with tau_e(r) = 0 (lower exclusion by e at b_lo)."""
    q, s = divmod(e, n)
    # (q + s*r) ≡ 0 mod n  =>  r = -q * s^{-1} mod n
    return (-q * pow(s, -1, n)) % n


def a_high_of(e: int, n: int) -> int:
    """Residue r with tau_e(r) = n-1 (upper exclusion by e at b_lo)."""
    q, s = divmod(e, n)
    # (q + s*r) ≡ n-1 mod n  =>  r = (n-1-q) * s^{-1} mod n
    return ((n - 1 - q) * pow(s, -1, n)) % n


# ---------------------------------------------------------------------------
# Per-residue classification
# ---------------------------------------------------------------------------

def classify_residue(
    n: int,
    e_non: tuple[int, ...],
    L: int,
    b_lo: int,
    budget: float,
    safe_sets_map: dict[int, set[int]],
    r: int,
) -> dict:
    """
    Classify residue r for the given Case-B tuple.

    Returns a dict with all fields. Residues with |Excl| > 3 are flagged
    but not deeply analyzed (blockers left empty).
    """
    excl_list = [e for e in e_non if r not in safe_sets_map[e]]
    k = len(excl_list)

    result: dict = {
        "r": r,
        "interior": int(1 <= r <= n - 2),
        "excl_multiplicity": k,
        "excl_set": "|".join(str(e) for e in excl_list),
        "cap": 0,
        "budget_ok": 0,
        "valid": 0,
        "n_blockers": 0,
        "blocker_runners": "",
        "blocker_taus": "",
        "blocker_ces": "",
        "blocker_strips": "",
        "blocker_windows": "",
        "cascade_runners": "",
        "cascade_a_highs": "",
        "cascade_a_lows": "",
    }

    # k=0: r is safe for all runners => r in A_{b_lo}, impossible in Case B interior
    # k>3: too many excluders, skip deep analysis
    if k == 0 or k > 3:
        return result

    # Arrivals for each excluder
    arrivals = {e: arrival_time(e, r, b_lo, L, n) for e in excl_list}
    cap = max(arrivals.values())
    budget_ok = int(cap <= budget)

    result["cap"] = cap
    result["budget_ok"] = budget_ok

    # Dominant excluder: the one with the maximum arrival (breaks ties by value)
    e_dom = max(excl_list, key=lambda e: (arrivals[e], e))
    zone_dom = zone_at_blo(e_dom, r, n)

    # Sanity: excluders must be in lower or upper zone
    if zone_dom not in ("lower", "upper"):
        raise AssertionError(
            f"Excluder e_dom={e_dom} of r={r} has zone='safe' — contradiction "
            f"(n={n}, tau={tau_index(e_dom, r, n)})"
        )

    zone_num_dom = zone_arrival_numerator(e_dom, zone_dom, n)

    # Classify each co-covering runner
    blocker_runners = []
    blocker_taus = []
    blocker_ces = []
    blocker_strips = []
    blocker_windows = []
    cascade_runners = []
    cascade_a_highs = []
    cascade_a_lows = []

    for e_cov in e_non:
        if e_cov in excl_list:
            continue  # Not a co-covering runner; it excludes r
        if r not in safe_sets_map[e_cov]:
            continue  # Also excluded (shouldn't happen given excl_list is complete)

        tau = tau_index(e_cov, r, n)
        window = window_from_blo(e_cov, r, b_lo, L, n)
        assert window is not None, (
            f"Runner {e_cov} covers r={r} (in safe_set) but window_from_blo=None"
        )

        c_e = strip_threshold(e_cov, e_dom, zone_num_dom, n)
        strip = forbidden_tau_strip(e_cov, e_dom, zone_num_dom, n)
        blocks = int(window < cap)

        # Verify strip ↔ window equivalence for k=1 (guaranteed by derivation)
        if k == 1:
            blocks_strip = int(strip is not None and strip[0] <= tau <= strip[1])
            assert blocks == blocks_strip, (
                f"k=1 strip/window mismatch: n={n} r={r} e_cov={e_cov} e_dom={e_dom} "
                f"window={window} cap={cap} tau={tau} strip={strip} c_e={c_e}"
            )

        if blocks:
            blocker_runners.append(str(e_cov))
            blocker_taus.append(str(tau))
            blocker_ces.append(str(c_e))
            blocker_strips.append(
                f"{strip[0]}-{strip[1]}" if strip else "none"
            )
            blocker_windows.append(str(window))
            cascade_runners.append(str(e_cov))
            cascade_a_highs.append(str(a_high_of(e_cov, n)))
            cascade_a_lows.append(str(a_low_of(e_cov, n)))

    valid = int(budget_ok and len(blocker_runners) == 0)

    result.update({
        "valid": valid,
        "n_blockers": len(blocker_runners),
        "blocker_runners": "|".join(blocker_runners),
        "blocker_taus": "|".join(blocker_taus),
        "blocker_ces": "|".join(blocker_ces),
        "blocker_strips": "|".join(blocker_strips),
        "blocker_windows": "|".join(blocker_windows),
        "cascade_runners": "|".join(cascade_runners),
        "cascade_a_highs": "|".join(cascade_a_highs),
        "cascade_a_lows": "|".join(cascade_a_lows),
    })

    return result


# ---------------------------------------------------------------------------
# Tuple-level analysis
# ---------------------------------------------------------------------------

def analyze_case_b_tuple(
    n: int,
    e_non: tuple[int, ...],
) -> tuple[list[dict], int, float] | None:
    """
    Analyze a single tuple.

    Returns (per_residue_rows, L, budget) if the tuple is Case B,
    else None (Case A, or invalid tuple).
    """
    e_non = tuple(sorted(e_non))

    if 1 not in e_non:
        return None
    if not is_prime(n):
        return None
    if any(gcd(e, n) != 1 for e in e_non):
        return None

    e_all = list(e_non) + [n]
    if gcd_list(e_all) != 1:
        return None

    L = lcm_list(e_all)
    b_lo = L // n
    budget = (n - 2) * (L - n) / (2 * n)
    safe_sets_map = {e: safe_set(e, b_lo, L, n) for e in e_non}

    # Case B: A_{b_lo} = intersection of all safe_sets must be empty
    ab_lo: set[int] = set(range(n))
    for e in e_non:
        ab_lo &= safe_sets_map[e]
    if ab_lo:
        return None  # Case A

    rows = []
    for r in range(n):
        row = classify_residue(n, e_non, L, b_lo, budget, safe_sets_map, r)
        # Embed tuple-level fields into each row
        row["n"] = n
        row["e_non"] = ",".join(str(e) for e in e_non)
        row["L"] = L
        row["b_lo"] = b_lo
        row["budget"] = f"{budget:.6f}"
        rows.append(row)

    return rows, L, budget


# ---------------------------------------------------------------------------
# Sweep and output
# ---------------------------------------------------------------------------

_FIELDNAMES = [
    "n", "e_non", "L", "b_lo", "budget",
    "r", "interior",
    "excl_multiplicity", "excl_set", "cap", "budget_ok", "valid",
    "n_blockers",
    "blocker_runners", "blocker_taus", "blocker_ces",
    "blocker_strips", "blocker_windows",
    "cascade_runners", "cascade_a_highs", "cascade_a_lows",
]


def run_sweep(
    n_values,
    max_e_factor: int,
    max_per_n: int,
    output_dir: str,
) -> None:
    rows_csv = os.path.join(output_dir, "lrc_br_witness_classifier_rows_v1.csv")
    summary_md = os.path.join(output_dir, "lrc_br_witness_classifier_summary_v1.md")

    all_rows: list[dict] = []
    per_n_stats: dict[int, dict] = {}

    for n in n_values:
        if not is_prime(n):
            continue

        unit_speeds = [
            e for e in range(1, max_e_factor * n + 1)
            if e != n and gcd(e, n) == 1
        ]

        checked = 0
        case_b_count = 0
        tuple_records: list[dict] = []

        for combo in combinations(unit_speeds, n - 2):
            if checked >= max_per_n:
                break
            if 1 not in combo:
                continue

            result = analyze_case_b_tuple(n, combo)
            checked += 1

            if result is None:
                continue

            rows, L, budget = result
            case_b_count += 1
            all_rows.extend(rows)

            # Tuple-level witness classification (interior residues only)
            interior = [
                row for row in rows
                if row["interior"] and 1 <= row["excl_multiplicity"] <= 3
            ]
            valid_int = [row for row in interior if row["valid"]]

            valid_k1 = [r for r in valid_int if r["excl_multiplicity"] == 1]
            valid_k2 = [r for r in valid_int if r["excl_multiplicity"] == 2]
            valid_k3 = [r for r in valid_int if r["excl_multiplicity"] == 3]
            valid_k_le_2 = [r for r in valid_int if r["excl_multiplicity"] <= 2]

            min_k = min(
                (row["excl_multiplicity"] for row in valid_int), default=None
            )

            tuple_records.append({
                "e_non": ",".join(str(e) for e in sorted(combo)),
                "L": L,
                "budget": budget,
                "has_valid_k1": bool(valid_k1),
                "has_valid_k2": bool(valid_k2),
                "has_valid_k3": bool(valid_k3),
                "has_valid_k_le_2": bool(valid_k_le_2),
                "min_valid_k": min_k,
                "no_valid_witness": (min_k is None),
            })

        # Per-n console output
        n_k1 = sum(1 for t in tuple_records if t["has_valid_k1"])
        n_need_k2 = sum(
            1 for t in tuple_records
            if not t["has_valid_k1"] and t["has_valid_k_le_2"]
        )
        n_k3_only = sum(
            1 for t in tuple_records
            if not t["has_valid_k_le_2"] and t["has_valid_k3"]
        )
        n_no_valid = sum(1 for t in tuple_records if t["no_valid_witness"])

        print(
            f"n={n}: checked={checked} case_b={case_b_count} "
            f"valid_k1={n_k1} need_k2={n_need_k2} "
            f"k3_only={n_k3_only} no_valid={n_no_valid}"
        )
        if n_no_valid > 0:
            print("  ALERT: hypothesis potentially falsified for this n")

        per_n_stats[n] = {
            "checked": checked,
            "case_b": case_b_count,
            "records": tuple_records,
        }

    # Write CSV
    with open(rows_csv, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=_FIELDNAMES)
        writer.writeheader()
        writer.writerows(all_rows)
    print(f"\nWrote {len(all_rows)} rows to {rows_csv}")

    # Write summary
    _write_summary(per_n_stats, summary_md)
    print(f"Wrote summary to {summary_md}")


def _write_summary(per_n_stats: dict, path: str) -> None:
    lines = [
        "# LRC BR Witness Classifier Summary",
        "",
        "**Date:** 2026-03-06",
        "**Script:** `lrc_br_witness_classifier_v1.py`",
        "**Branch hypothesis:** Every Case-B tuple (prime n, 1∈E_non) has a valid",
        "low-multiplicity witness r* with |Excl(r*)| ≤ 2.",
        "",
        "## Decision Gate",
        "",
        "> If any Case-B tuple has NO valid k≤2 witness (interior residue, budget ok,",
        "> all co-covering runners maintain window): the k≤2 hypothesis is falsified",
        "> and the G4BI roadmap pivot activates.",
        "",
        "## Definitions",
        "",
        "- **k**: excl_multiplicity = |{e ∈ E_non : r ∉ safe_set(e, b_lo)}|",
        "- **cap**: max arr(e, r) over excl_set",
        "- **budget_ok**: cap ≤ (n−2)(L−n)/(2n)",
        "- **blocker**: co-covering runner e with window_from_blo(e,r) < cap",
        "- **valid**: budget_ok AND no blockers",
        "- **strip**: full forbidden tau strip {n−c_e,...,n−2} (size c_e−1 ≥ 1)",
        "- **c_e formula**: c_e = ceil((e·A_zone(e*) + e*·s_e) / (n·e*))",
        "",
    ]

    total_case_b = 0
    total_k1 = 0
    total_need_k2 = 0
    total_k3_only = 0
    total_no_valid = 0

    for n, stats in sorted(per_n_stats.items()):
        records = stats["records"]
        total_case_b += stats["case_b"]

        n_k1 = sum(1 for t in records if t["has_valid_k1"])
        n_need_k2 = sum(
            1 for t in records
            if not t["has_valid_k1"] and t["has_valid_k_le_2"]
        )
        n_k3_only = sum(
            1 for t in records
            if not t["has_valid_k_le_2"] and t["has_valid_k3"]
        )
        n_no_valid = sum(1 for t in records if t["no_valid_witness"])

        total_k1 += n_k1
        total_need_k2 += n_need_k2
        total_k3_only += n_k3_only
        total_no_valid += n_no_valid

        lines.extend([
            f"## n = {n}",
            "",
            f"- Checked: {stats['checked']}",
            f"- Case-B tuples: {stats['case_b']}",
            f"- Tuples with valid k=1 witness: {n_k1}",
            f"- Tuples needing k=2 (no valid k=1, has valid k≤2): {n_need_k2}",
            f"- Tuples with valid k=3 only (k≤2 insufficient): {n_k3_only}",
            f"- **Tuples with NO valid k≤3 witness: {n_no_valid}**",
            "",
        ])

        if n_no_valid > 0:
            lines.append("### HYPOTHESIS FALSIFIED — examples:")
            for t in records:
                if t["no_valid_witness"]:
                    lines.append(
                        f"  - E_non=({t['e_non']}), L={t['L']}, "
                        f"budget={t['budget']:.3f}"
                    )
            lines.append("")

        if n_k3_only > 0:
            lines.append("### Tuples requiring k=3 (k≤2 insufficient):")
            for t in records:
                if not t["has_valid_k_le_2"] and t["has_valid_k3"]:
                    lines.append(
                        f"  - E_non=({t['e_non']}), L={t['L']}, "
                        f"budget={t['budget']:.3f}"
                    )
            lines.append("")

    lines.extend([
        "## Overall Summary",
        "",
        f"- Total Case-B tuples analyzed: {total_case_b}",
        f"- Tuples with valid k=1 witness: {total_k1}",
        f"- Tuples needing k=2 (no k=1, has k≤2): {total_need_k2}",
        f"- Tuples with valid k=3 only (k≤2 fails): {total_k3_only}",
        f"- **Tuples with NO valid k≤3 witness: {total_no_valid}**",
        "",
    ])

    if total_no_valid == 0 and total_k3_only == 0:
        lines.extend([
            "### HYPOTHESIS STATUS: k≤2 HOLDS",
            "",
            "All Case-B tuples in this sweep have a valid k≤2 witness.",
            "The low-multiplicity-2 branch hypothesis is supported.",
            "Proceed to Phase 1 (cascade diagnostic) and Phase 3 (proof routes).",
            "",
        ])
    elif total_no_valid == 0:
        lines.extend([
            "### HYPOTHESIS STATUS: k≤3 holds; k≤2 FALSIFIED",
            "",
            f"{total_k3_only} tuples require k=3 witness (no valid k≤2).",
            "The k≤2 hypothesis fails; widen branch to k≤3.",
            "Review k=3-only tuples for structural pattern before proceeding.",
            "",
        ])
    else:
        lines.extend([
            "### HYPOTHESIS STATUS: LOW-MULTIPLICITY ROUTE FALSIFIED",
            "",
            f"{total_no_valid} Case-B tuples have no valid k≤3 witness.",
            "**G4BI roadmap pivot activates immediately.**",
            "",
        ])

    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Phase 0 classifier: enumerate valid low-multiplicity witnesses "
            "for Case-B tuples (Lemma BR branch attempt)"
        )
    )
    parser.add_argument(
        "--n-min", type=int, default=5,
        help="minimum n for sweep (default: 5)"
    )
    parser.add_argument(
        "--n-max", type=int, default=13,
        help="maximum n for sweep (default: 13)"
    )
    parser.add_argument(
        "--max-e-factor", type=int, default=4,
        help="search bound: e <= factor * n (default: 4)"
    )
    parser.add_argument(
        "--max-per-n", type=int, default=200,
        help="max Case-B tuples to analyze per n (default: 200)"
    )
    parser.add_argument(
        "--output-dir", type=str, default=".",
        help="output directory for CSV and summary (default: current dir)"
    )
    args = parser.parse_args()

    os.makedirs(args.output_dir, exist_ok=True)

    run_sweep(
        n_values=range(args.n_min, args.n_max + 1),
        max_e_factor=args.max_e_factor,
        max_per_n=args.max_per_n,
        output_dir=args.output_dir,
    )


if __name__ == "__main__":
    main()
