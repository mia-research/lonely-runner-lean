#!/usr/bin/env python3
"""
Gap 4 / S3 Composite-n Diagnostic  (v1)
========================================
Goal: Understand WHY x_0 >= n-1 holds for composite n in Case-2,
      since the prime-n anchor z-property argument does not directly extend.

For each Case-2 tuple we compute:
  - Per-fiber delta(b) for all b in B_div
  - Per-anchor z-profile and bad_a union
  - Block structure of safe/obstructed regions along B_div
  - Obstruction signature census (t_e, z_e) for fully-obstructed fibers
  - Tight-tuple anatomy (when B_safe = n-1)

Candidate analytic routes being probed:
  Route A: Generalized z-property — good anchors (b_j with z_e=1 for all e in E_non)
           always provide enough non-obstructed mass.
  Route B: Obstructed regions are bounded-length blocks; safe regions always total >= n-1.
  Route C: Overlap structure of bad_a cosets means full coverage is rare.

Outputs:
  lrc_gap4_s3_composite_diag_rows_v1.csv   — one row per tuple
  lrc_gap4_s3_composite_diag_tight_v1.csv  — detailed anatomy for tight tuples (B_safe=n-1)
  lrc_gap4_s3_composite_diag_obstrsig_v1.csv — obstruction signatures census
  lrc_gap4_s3_composite_diag_summary_v1.md — human-readable summary

"""
from __future__ import annotations

import csv
import math
import random
from collections import Counter
from itertools import product

PROOF_DIR = "/Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01"

OUT_ROWS    = f"{PROOF_DIR}/lrc_gap4_s3_composite_diag_rows_v1.csv"
OUT_TIGHT   = f"{PROOF_DIR}/lrc_gap4_s3_composite_diag_tight_v1.csv"
OUT_OSIG    = f"{PROOF_DIR}/lrc_gap4_s3_composite_diag_obstrsig_v1.csv"
OUT_SUMMARY = f"{PROOF_DIR}/lrc_gap4_s3_composite_diag_summary_v1.md"

# Exhaustive: composite n only (4, 6)
MAX_E_EXH = {4: 9, 6: 8}
L_CAP_EXH = 5000   # skip very large-L tuples in exhaustive pass

# Random stress: composite n
RANDOM_CFG = [
    (8,  14, 300),
    (9,  14, 300),
    (10, 14, 250),
    (12, 14, 200),
]
L_CAP_RANDOM = 3000

# Also exhaustive for primes to compare behaviour
MAX_E_EXH_PRIME = {5: 7, 7: 7}


def euler_phi(n: int) -> int:
    r, x = n, n
    p = 2
    while p * p <= x:
        if x % p == 0:
            while x % p == 0:
                x //= p
            r -= r // p
        p += 1
    if x > 1:
        r -= r // x
    return r


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for p in range(2, int(n**0.5) + 1):
        if n % p == 0:
            return False
    return True


def bad_a_set(e: int, b: int, L: int, N: int, n: int) -> frozenset[int]:
    """
    Return the set of a in {0,...,n-1} that are unsafe for non-divisible speed e at fiber b.
    k = a*L + b.
    Unsafe iff (e*k mod N) < L  OR  (e*k mod N) > (n-1)*L.
    Uses the exact formula:
      e*b = t_e*L + r_e  (t_e = floor(eb/L), r_e = eb mod L)
      e*(aL+b) mod N = n*(e*a + t_e)... NO -- use direct computation.
    Direct is fastest and unambiguous.
    """
    lo, hi = L, (n - 1) * L
    bad = set()
    for a in range(n):
        k = a * L + b
        x = (e * k) % N
        if x < lo or x > hi:
            bad.add(a)
    return frozenset(bad)


def z_profile(E_non: list[int], b: int, L: int) -> dict[int, int]:
    """
    For each e in E_non, return z_e(b) = 1 if (e*b mod L) > 0, else 0.
    Also return t_e(b) = floor(e*b / L).
    Returns dict mapping e -> (t_e, z_e).
    """
    result = {}
    for e in E_non:
        eb = e * b
        t = eb // L
        r = eb % L
        result[e] = (t, 1 if r > 0 else 0)
    return result


def analyze_full(E: tuple[int, ...], n: int) -> dict:
    """
    Full per-fiber analysis of a Case-2 tuple.
    Returns:
      - B_div, B_safe, x0
      - per-anchor stats
      - block structure
      - obstruction signatures
    """
    L = math.lcm(*E)
    N = n * L
    lo, hi = L, (n - 1) * L

    E_div = [e for e in E if e % n == 0]
    E_non = [e for e in E if e % n != 0]
    k_div = len(E_div)
    k_non = len(E_non)

    # --- Pass 1: compute delta(b) for all b in B_div ---
    delta_list = []   # (b, delta_b)
    for b in range(L):
        # divisible gate
        ok = True
        for e in E_div:
            x = (e * b) % N
            if x < lo or x > hi:
                ok = False
                break
        if not ok:
            continue

        # count safe a-values
        d = 0
        for a in range(n):
            k = a * L + b
            safe = True
            for e in E_non:
                x = (e * k) % N
                if x < lo or x > hi:
                    safe = False
                    break
            if safe:
                d += 1
        delta_list.append((b, d))

    B_div   = len(delta_list)
    x0      = sum(d for _, d in delta_list)
    B_safe  = sum(1 for _, d in delta_list if d > 0)

    # --- Anchor analysis ---
    # Anchors b_j = j*L//n for j=0,...,n-1
    anchor_stats = []
    for j in range(n):
        b_j = (j * L) // n
        # check divisible gate
        in_bdiv = True
        for e in E_div:
            x = (e * b_j) % N
            if x < lo or x > hi:
                in_bdiv = False
                break

        if not in_bdiv:
            anchor_stats.append({
                "j": j, "b_j": b_j, "in_bdiv": False,
                "delta": -1, "z_all_1": False,
                "union_bad_size": -1
            })
            continue

        # z-profile
        zp = z_profile(E_non, b_j, L)
        z_all_1 = all(z == 1 for (_, z) in zp.values())

        # bad_a union
        union_bad = set()
        for e in E_non:
            union_bad |= bad_a_set(e, b_j, L, N, n)
        union_bad_size = len(union_bad)

        # delta
        delta_bj = n - union_bad_size  # = n - |union_bad|
        # verify against direct count
        delta_direct = sum(
            1 for a in range(n)
            if all(
                lo <= (e * (a * L + b_j)) % N <= hi
                for e in E_non
            )
        )

        anchor_stats.append({
            "j": j, "b_j": b_j, "in_bdiv": True,
            "delta": delta_direct,
            "z_all_1": z_all_1,
            "union_bad_size": union_bad_size,
            "zp": zp,
        })

    # Derived anchor metrics
    anchors_in_bdiv = sum(1 for a in anchor_stats if a["in_bdiv"])
    good_anchors = sum(1 for a in anchor_stats if a["in_bdiv"] and a["z_all_1"])
    # "good" = in B_div AND z_e=1 for all non-div speeds
    good_anchor_delta_sum = sum(
        a["delta"] for a in anchor_stats
        if a["in_bdiv"] and a["z_all_1"] and a["j"] >= 1
    )
    # non-trivial good anchors with delta > 0
    good_nontrivial_safe = sum(
        1 for a in anchor_stats
        if a["in_bdiv"] and a["z_all_1"] and a["j"] >= 1 and a["delta"] > 0
    )
    # max union_bad size over good non-trivial anchors
    good_max_union = max(
        (a["union_bad_size"] for a in anchor_stats
         if a["in_bdiv"] and a["z_all_1"] and a["j"] >= 1),
        default=-1
    )
    # anchor_x0 = sum of delta over all non-trivial anchors in B_div
    anchor_x0 = sum(
        a["delta"] for a in anchor_stats
        if a["in_bdiv"] and a["j"] >= 1
    )

    # --- Block structure of B_div walk ---
    # Compute runs of safe vs obstructed b's
    if delta_list:
        b_values = [b for b, _ in delta_list]
        delta_vals = [d for _, d in delta_list]

        # Count connected runs (by index in delta_list, not by b value)
        n_safe_runs = 0
        n_obstr_runs = 0
        max_safe_run = 0
        max_obstr_run = 0
        cur_safe_run = 0
        cur_obstr_run = 0

        for d in delta_vals:
            if d > 0:
                cur_safe_run += 1
                if cur_obstr_run > 0:
                    n_obstr_runs += 1
                    max_obstr_run = max(max_obstr_run, cur_obstr_run)
                    cur_obstr_run = 0
            else:
                cur_obstr_run += 1
                if cur_safe_run > 0:
                    n_safe_runs += 1
                    max_safe_run = max(max_safe_run, cur_safe_run)
                    cur_safe_run = 0
        if cur_safe_run > 0:
            n_safe_runs += 1
            max_safe_run = max(max_safe_run, cur_safe_run)
        if cur_obstr_run > 0:
            n_obstr_runs += 1
            max_obstr_run = max(max_obstr_run, cur_obstr_run)
    else:
        n_safe_runs = n_obstr_runs = 0
        max_safe_run = max_obstr_run = 0

    # --- Obstruction signature census ---
    # For each obstructed b (delta=0), record (tuple of (t_e, z_e) for e in sorted E_non)
    osig_counter: Counter = Counter()
    for b, d in delta_list:
        if d == 0:
            zp = z_profile(E_non, b, L)
            sig = tuple((e, zp[e][0], zp[e][1]) for e in sorted(set(E_non)))
            osig_counter[sig] += 1

    return {
        "L": L,
        "N": N,
        "k_div": k_div,
        "k_non": k_non,
        "B_div": B_div,
        "B_safe": B_safe,
        "x0": x0,
        "tight": int(B_safe == n - 1),
        # anchor metrics
        "anchors_in_bdiv": anchors_in_bdiv,
        "good_anchors": good_anchors,           # j>=0, z_e=1 all non-div
        "good_nontrivial_safe": good_nontrivial_safe,  # j>=1, safe AND good
        "good_anchor_delta_sum": good_anchor_delta_sum,
        "anchor_x0": anchor_x0,
        "good_max_union": good_max_union,
        # block structure
        "n_safe_runs": n_safe_runs,
        "n_obstr_runs": n_obstr_runs,
        "max_safe_run": max_safe_run,
        "max_obstr_run": max_obstr_run,
        # detailed
        "anchor_stats": anchor_stats,
        "delta_list": delta_list,
        "osig_counter": osig_counter,
    }


def process_block(block_label: str, tuples_iter, n: int,
                  rows: list[dict], tight_rows: list[dict],
                  osig_rows: list[dict], summary_parts: list[str],
                  phi_n: int, l_cap: int | None = None):
    """Process one block of tuples (exhaustive or random)."""
    counts = {
        "total": 0, "viol_x0": 0, "viol_bsafe": 0,
        "tight": 0, "good_anchor_zero": 0,
    }
    mins = {}

    def upd(key, val, ref):
        if key not in mins or val < mins[key][0]:
            mins[key] = (val, ref)

    for E in tuples_iter:
        if math.gcd(*E) != 1:
            continue
        if not any(e % n == 0 for e in E):
            continue
        if l_cap is not None:
            L = math.lcm(*E)
            if L > l_cap:
                continue

        counts["total"] += 1
        t = analyze_full(E, n)

        if t["x0"] < n - 1:
            counts["viol_x0"] += 1
        if t["B_safe"] < n - 1:
            counts["viol_bsafe"] += 1
        if t["tight"]:
            counts["tight"] += 1
        if t["good_anchors"] == 0:
            counts["good_anchor_zero"] += 1

        e_str = " ".join(map(str, E))
        upd("x0", t["x0"], e_str)
        upd("B_safe", t["B_safe"], e_str)
        upd("good_anchors", t["good_anchors"], e_str)
        upd("good_nontrivial_safe", t["good_nontrivial_safe"], e_str)
        upd("max_obstr_run", t["max_obstr_run"], e_str)

        row = {
            "block": block_label,
            "n": n,
            "phi_n": phi_n,
            "e_tuple": e_str,
            "L": t["L"],
            "k_div": t["k_div"],
            "k_non": t["k_non"],
            "B_div": t["B_div"],
            "B_safe": t["B_safe"],
            "x0": t["x0"],
            "tight": t["tight"],
            "anchors_in_bdiv": t["anchors_in_bdiv"],
            "good_anchors": t["good_anchors"],
            "good_nontrivial_safe": t["good_nontrivial_safe"],
            "good_anchor_delta_sum": t["good_anchor_delta_sum"],
            "anchor_x0": t["anchor_x0"],
            "good_max_union": t["good_max_union"],
            "n_safe_runs": t["n_safe_runs"],
            "n_obstr_runs": t["n_obstr_runs"],
            "max_safe_run": t["max_safe_run"],
            "max_obstr_run": t["max_obstr_run"],
        }
        rows.append(row)

        # tight anatomy
        if t["tight"]:
            safe_b = [(b, d) for b, d in t["delta_list"] if d > 0]
            obstr_b = [(b, d) for b, d in t["delta_list"] if d == 0]
            for b, d in safe_b:
                zp = z_profile([e for e in E if e % n != 0], b, t["L"])
                tight_rows.append({
                    "n": n, "e_tuple": e_str, "L": t["L"],
                    "b": b, "delta": d, "is_anchor": int(b * n % t["L"] == 0),
                    "z_profile": str({e: zp[e] for e in sorted(set(e for e in E if e % n != 0))}),
                    "type": "safe"
                })
            # also record a sample of obstructed
            for b, d in obstr_b[:5]:
                zp = z_profile([e for e in E if e % n != 0], b, t["L"])
                tight_rows.append({
                    "n": n, "e_tuple": e_str, "L": t["L"],
                    "b": b, "delta": d, "is_anchor": int(b * n % t["L"] == 0),
                    "z_profile": str({e: zp[e] for e in sorted(set(e for e in E if e % n != 0))}),
                    "type": "obstr_sample"
                })

        # obstruction signatures (collect top ones)
        for sig, cnt in t["osig_counter"].items():
            osig_rows.append({
                "block": block_label, "n": n, "e_tuple": e_str,
                "L": t["L"], "k_div": t["k_div"],
                "signature": str(sig), "count": cnt,
                "frac_of_bdiv": f"{cnt / t['B_div']:.4f}" if t["B_div"] > 0 else "0"
            })

    # summary for this block
    summary_parts.append(f"\n### {block_label} (n={n})")
    summary_parts.append(f"- Tuples processed: {counts['total']}")
    summary_parts.append(f"- viol(x0 >= n-1): {counts['viol_x0']}")
    summary_parts.append(f"- viol(B_safe >= n-1): {counts['viol_bsafe']}")
    summary_parts.append(f"- Tight (B_safe = n-1): {counts['tight']}")
    summary_parts.append(f"- good_anchors = 0 (no good anchor): {counts['good_anchor_zero']}")

    if "x0" in mins:
        summary_parts.append(f"- min x0: {mins['x0'][0]}  at E={mins['x0'][1]}")
    if "B_safe" in mins:
        summary_parts.append(f"- min B_safe: {mins['B_safe'][0]}  at E={mins['B_safe'][1]}")
    if "good_anchors" in mins:
        summary_parts.append(f"- min good_anchors: {mins['good_anchors'][0]}  at E={mins['good_anchors'][1]}")
    if "good_nontrivial_safe" in mins:
        summary_parts.append(f"- min good_nontrivial_safe (j>=1 anchors that are good AND safe): {mins['good_nontrivial_safe'][0]}  at E={mins['good_nontrivial_safe'][1]}")
    if "max_obstr_run" in mins:
        summary_parts.append(f"- min max_obstr_run: {mins['max_obstr_run'][0]}  at E={mins['max_obstr_run'][1]}")


def main():
    random.seed(42)
    rows: list[dict] = []
    tight_rows: list[dict] = []
    osig_rows: list[dict] = []
    summary_parts: list[str] = []

    summary_parts.append("# Gap 4 / S3 Composite-n Diagnostic (v1)")
    summary_parts.append("")
    summary_parts.append("## Purpose")
    summary_parts.append("Probe the structure of non-obstructed fibers for composite n in Case-2,")
    summary_parts.append("looking for patterns that could support an analytic proof.")
    summary_parts.append("")
    summary_parts.append("## Key Metrics")
    summary_parts.append("- `good_anchors`: #{j in {0,...,n-1}: b_j in B_div AND z_e=1 for all e in E_non}")
    summary_parts.append("- `good_nontrivial_safe`: #{j>=1 good anchors with delta(b_j)>0}")
    summary_parts.append("- `max_obstr_run`: longest consecutive obstructed block in B_div walk")
    summary_parts.append("- `n_safe_runs`: number of connected safe regions in B_div")
    summary_parts.append("- `tight`: B_safe = n-1 exactly")
    summary_parts.append("")

    # --- Exhaustive blocks ---
    summary_parts.append("## Exhaustive Results")

    # Composite n
    for n, max_e in sorted(MAX_E_EXH.items()):
        phi_n = euler_phi(n)
        label = f"exhaustive_composite_n{n}"
        E_iter = product(range(1, max_e + 1), repeat=n - 1)
        process_block(label, E_iter, n, rows, tight_rows, osig_rows,
                      summary_parts, phi_n, l_cap=L_CAP_EXH)

    # Prime n for comparison
    for n, max_e in sorted(MAX_E_EXH_PRIME.items()):
        phi_n = euler_phi(n)
        label = f"exhaustive_prime_n{n}"
        E_iter = product(range(1, max_e + 1), repeat=n - 1)
        process_block(label, E_iter, n, rows, tight_rows, osig_rows,
                      summary_parts, phi_n, l_cap=L_CAP_EXH)

    # --- Random stress blocks ---
    summary_parts.append("\n## Random Stress Results")

    for n, max_e, target in RANDOM_CFG:
        phi_n = euler_phi(n)
        label = f"random_n{n}"
        kept = 0
        tries = 0

        def gen():
            nonlocal kept, tries
            while kept < target and tries < target * 200:
                tries += 1
                E = tuple(random.randint(1, max_e) for _ in range(n - 1))
                if math.gcd(*E) != 1:
                    continue
                if not any(e % n == 0 for e in E):
                    continue
                L = math.lcm(*E)
                if L > L_CAP_RANDOM:
                    continue
                kept += 1
                yield E

        process_block(label, gen(), n, rows, tight_rows, osig_rows,
                      summary_parts, phi_n)

    # --- Analytic hypotheses section ---
    summary_parts.append("\n## Analytic Hypotheses Check")
    summary_parts.append("")
    summary_parts.append("Based on above data:")
    summary_parts.append("")

    # Count evidence for Route A
    route_a_support = sum(1 for r in rows if r.get("good_nontrivial_safe", 0) >= r["n"] - 1
                          if "n" in r)
    total_composite = sum(1 for r in rows if not is_prime(r["n"]))
    summary_parts.append(f"### Route A (good non-trivial anchors cover n-1 by themselves)")
    summary_parts.append(f"- Tuples where good_nontrivial_safe >= n-1: {route_a_support} / {len(rows)}")
    summary_parts.append(f"- Composite n tuples: {total_composite}")
    summary_parts.append("")

    # Check: does good_nontrivial_safe = 0 ever occur?
    zero_good = [r for r in rows if r.get("good_nontrivial_safe", 1) == 0]
    summary_parts.append(f"### Cases with good_nontrivial_safe = 0")
    summary_parts.append(f"- Count: {len(zero_good)}")
    for r in zero_good[:10]:
        summary_parts.append(f"  - n={r['n']}, E={r['e_tuple']}, L={r['L']}, B_safe={r['B_safe']}, x0={r['x0']}")
    summary_parts.append("")

    # Check block structure for composite vs prime
    composite_rows = [r for r in rows if not is_prime(r["n"])]
    if composite_rows:
        max_obstr_vals = [r["max_obstr_run"] for r in composite_rows]
        summary_parts.append("### Obstruction block structure (composite n)")
        summary_parts.append(f"- max(max_obstr_run): {max(max_obstr_vals)}")
        summary_parts.append(f"- mean(max_obstr_run): {sum(max_obstr_vals)/len(max_obstr_vals):.1f}")
        summary_parts.append(f"- Tuples with max_obstr_run > B_div - (n-1):")
        bad_block = [r for r in composite_rows if r["max_obstr_run"] > r["B_div"] - (r["n"] - 1)]
        summary_parts.append(f"  Count: {len(bad_block)}")
        for r in bad_block[:5]:
            summary_parts.append(f"  - n={r['n']}, E={r['e_tuple']}, max_obstr_run={r['max_obstr_run']}, B_div={r['B_div']}, B_safe={r['B_safe']}")
    summary_parts.append("")

    # Tight tuple summary
    tight_all = [r for r in rows if r["tight"]]
    summary_parts.append(f"### Tight tuples (B_safe = n-1)")
    summary_parts.append(f"- Total tight tuples: {len(tight_all)}")
    tight_regimes = Counter()
    for r in tight_all:
        regime = "L=n" if r["L"] == r["n"] else "L>n"
        tight_regimes[f"n={r['n']}_{regime}"] += 1
    for k, v in sorted(tight_regimes.items()):
        summary_parts.append(f"  - {k}: {v}")
    summary_parts.append("")

    # --- Write outputs ---
    if rows:
        with open(OUT_ROWS, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=[k for k in rows[0] if k != "anchor_stats"])
            w.writeheader()
            w.writerows(rows)
        print(f"wrote: {OUT_ROWS}  ({len(rows)} rows)")

    if tight_rows:
        with open(OUT_TIGHT, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(tight_rows[0].keys()))
            w.writeheader()
            w.writerows(tight_rows)
        print(f"wrote: {OUT_TIGHT}  ({len(tight_rows)} rows)")

    if osig_rows:
        with open(OUT_OSIG, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(osig_rows[0].keys()))
            w.writeheader()
            w.writerows(osig_rows)
        print(f"wrote: {OUT_OSIG}  ({len(osig_rows)} rows)")

    with open(OUT_SUMMARY, "w") as f:
        f.write("\n".join(summary_parts) + "\n")
    print(f"wrote: {OUT_SUMMARY}")


if __name__ == "__main__":
    main()
