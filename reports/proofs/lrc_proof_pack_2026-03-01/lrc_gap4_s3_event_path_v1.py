#!/usr/bin/env python3
"""
Gap 4 / S3 — Event-Cell Path Diagnostic (v1)
=============================================
Tests the Complementarity Bound Conjecture via event-cell decomposition.

Conjecture (CB): For any gcd-1 Case-2 tuple E with L>n,
    max_obstr_run  ≤  B_div − n
where max_obstr_run = length (in B_div fibers) of the longest fully-obstructed
consecutive block.

Key hypotheses probed:
  H1: n_safe_cells ≥ n always (for L>n)
  H2: max_obstr_fiber_run ≤ min(L/e − 1 : e ∈ E_non) always
  H3: Every obstructed run is contained within a single t-period of some runner e
  H4: period_bound_slack = (B_div − n + 1) − max(L/e) ≥ 0 always

Event boundary definition (from Lemma S2):
  For runner e ∈ E_non, t_e(b) = floor(e*b / L).
  t_e(b) increments by 1 when b crosses ceil(m*L/e) for m = 1,...,e-1.
  At b = m*L/e (exact multiple), z_e(b) = 0 (safe fiber by z=0 lemma if gcd(e,n)=1).
  Between multiples, z_e(b) = 1.

Cells = intervals between consecutive event-boundary b-values in B_div.
Within each cell, (t_e, z_e) is constant for all e, so bad_a union is constant.

Outputs:
  lrc_gap4_s3_event_path_rows_v1.csv       — one row per L>n tuple
  lrc_gap4_s3_event_path_tight_cells_v1.csv — full cell sequences for tight cases
  lrc_gap4_s3_event_path_termination_v1.csv — per-obstr-run termination type data
  lrc_gap4_s3_event_path_summary_v1.md     — human-readable summary
"""
from __future__ import annotations

import csv
import math
import random
from collections import Counter
from itertools import product

PROOF_DIR = "/Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01"

OUT_ROWS  = f"{PROOF_DIR}/lrc_gap4_s3_event_path_rows_v1.csv"
OUT_TIGHT = f"{PROOF_DIR}/lrc_gap4_s3_event_path_tight_cells_v1.csv"
OUT_TERM  = f"{PROOF_DIR}/lrc_gap4_s3_event_path_termination_v1.csv"
OUT_SUM   = f"{PROOF_DIR}/lrc_gap4_s3_event_path_summary_v1.md"

# Exhaustive (composite) + prime comparison
MAX_E_EXH       = {4: 9, 6: 8}
MAX_E_EXH_PRIME = {5: 7, 7: 7}
L_CAP_EXH       = 5000

# Random stress (composite n >= 8)
RANDOM_CFG = [
    (8,  14, 300),
    (9,  14, 300),
    (10, 14, 250),
    (12, 14, 200),
]
L_CAP_RANDOM = 3000


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

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
    """Exact bad a-values for runner e at fiber b. Direct computation."""
    lo, hi = L, (n - 1) * L
    bad: set[int] = set()
    for a in range(n):
        x = (e * (a * L + b)) % N
        if x < lo or x > hi:
            bad.add(a)
    return frozenset(bad)


def union_bad_size(E_non: list[int], b: int, L: int, N: int, n: int) -> int:
    """Size of union of bad_a sets for all non-divisible runners at fiber b."""
    union: set[int] = set()
    for e in E_non:
        union |= bad_a_set(e, b, L, N, n)
        if len(union) == n:
            return n  # early exit
    return len(union)


# ---------------------------------------------------------------------------
# Event-cell decomposition
# ---------------------------------------------------------------------------

def compute_event_boundaries(E_non: list[int], L: int, b_lo: int, b_hi: int) -> list[tuple[int, int]]:
    """
    Return sorted list of (b_val, runner_e) for event boundaries strictly inside
    the B_div range [b_lo, b_hi].  Each boundary marks where t_e(b) increments,
    i.e. b_val = ceil(m*L/e) for m=1,...,e-1 and e in E_non.
    Note: b_val = m*L/e (exact integer) is a z=0 event for runner e.
    """
    boundaries: list[tuple[int, int]] = []
    seen: set[int] = set()  # deduplicate b-values across runners
    for e in E_non:
        for m in range(1, e):
            # boundary at ceil(m*L/e) = floor((m*L + e - 1) / e)
            b_val = (m * L + e - 1) // e
            if b_lo <= b_val <= b_hi and b_val not in seen:
                seen.add(b_val)
                boundaries.append((b_val, e))
    boundaries.sort()
    return boundaries


def z_e_val(e: int, b: int, L: int) -> int:
    """z_e(b) = 1 if (e*b mod L) > 0, else 0."""
    return 1 if (e * b) % L != 0 else 0


def t_e_val(e: int, b: int, L: int) -> int:
    """t_e(b) = floor(e*b / L)."""
    return (e * b) // L


# ---------------------------------------------------------------------------
# Main per-tuple analysis
# ---------------------------------------------------------------------------

def analyze_event_path(E: tuple[int, ...], n: int) -> dict:
    """
    Full event-cell analysis of a Case-2 tuple with L > n.
    Returns per-tuple metrics + cell/run sequences.
    """
    L = math.lcm(*E)
    N = n * L
    lo_gate, hi_gate = L, (n - 1) * L

    E_div = [e for e in E if e % n == 0]
    E_non = [e for e in E if e % n != 0]
    k_div = len(E_div)
    k_non = len(E_non)

    # B_div range: fibers b in [0,L) passing divisible gate
    # For k_div=1 with e_d=n: b in [L/n, (n-1)L/n]
    # General: check gate directly
    b_div_list: list[int] = []
    for b in range(L):
        ok = True
        for e in E_div:
            x = (e * b) % N
            if x < lo_gate or x > hi_gate:
                ok = False
                break
        if ok:
            b_div_list.append(b)

    B_div_count = len(b_div_list)
    if B_div_count == 0:
        return None  # degenerate, skip

    b_lo = b_div_list[0]
    b_hi = b_div_list[-1]

    # Per-fiber delta
    delta_by_b: dict[int, int] = {}
    for b in b_div_list:
        ub = union_bad_size(E_non, b, L, N, n)
        delta_by_b[b] = n - ub

    B_safe = sum(1 for d in delta_by_b.values() if d > 0)
    x0     = sum(delta_by_b.values())

    # Existing max_obstr_run (over fibers)
    max_obstr_fiber = 0
    cur = 0
    for b in b_div_list:
        if delta_by_b[b] == 0:
            cur += 1
            max_obstr_fiber = max(max_obstr_fiber, cur)
        else:
            cur = 0

    # Runner periods
    periods: dict[int, float] = {e: L / e for e in set(E_non)}  # L/e (integer since e|L)
    min_period = min(periods.values()) if periods else float('inf')
    max_period = max(periods.values()) if periods else 0

    # --- Event-cell decomposition ---
    # Boundaries: sorted list of b-values where some t_e changes
    boundaries = compute_event_boundaries(E_non, L, b_lo, b_hi)
    boundary_bs = sorted({b for b, _ in boundaries} | {b_lo, b_hi + 1})
    # Remove duplicates and sort
    boundary_bs = sorted(set(boundary_bs))

    # Build cells: each cell is a maximal B_div interval with constant (t_e, z_e)
    # Cells are determined by consecutive boundary_bs
    cells: list[dict] = []
    boundary_set = {b for b, _ in boundaries}

    # Cell start points are: b_lo, and each boundary b-value in B_div
    cell_starts = sorted({b_lo} | {b for b, _ in boundaries if b in set(b_div_list)})

    for i, cs in enumerate(cell_starts):
        ce = cell_starts[i + 1] - 1 if i + 1 < len(cell_starts) else b_hi
        # fibers in this cell
        cell_fibers = [b for b in b_div_list if cs <= b <= ce]
        if not cell_fibers:
            continue
        b_rep = cell_fibers[0]
        sig = {e: (t_e_val(e, b_rep, L), z_e_val(e, b_rep, L)) for e in set(E_non)}
        delta_rep = delta_by_b[b_rep]
        is_safe = (delta_rep > 0)
        # What runner transitioned at cs?
        trans_runners = [r for b_bd, r in boundaries if b_bd == cs]
        cell = {
            "b_start": cs,
            "b_end": ce,
            "cell_len": len(cell_fibers),
            "safe": is_safe,
            "delta": delta_rep,
            "sig": sig,
            "trans_runners": trans_runners,
        }
        cells.append(cell)

    n_safe_cells  = sum(1 for c in cells if c["safe"])
    n_obstr_cells = sum(1 for c in cells if not c["safe"])

    # Max consecutive obstructed CELLS
    max_obstr_cells = 0
    cur_c = 0
    for c in cells:
        if not c["safe"]:
            cur_c += 1
            max_obstr_cells = max(max_obstr_cells, cur_c)
        else:
            cur_c = 0

    # --- Termination analysis ---
    # For each obstructed run (in fibers), identify the terminating events
    term_events: list[dict] = []
    in_run = False
    run_start_b = None
    run_start_idx = None

    b_status = [(b, delta_by_b[b] > 0) for b in b_div_list]
    for idx, (b, safe) in enumerate(b_status):
        if not in_run and not safe:
            in_run = True
            run_start_b = b
            run_start_idx = idx
        elif in_run and safe:
            run_end_b = b_status[idx - 1][0]
            run_len   = idx - run_start_idx
            # What transitioned to end this run?
            # Find the boundary just at or before b (the first safe fiber after run)
            # The safe fiber b is the start of a new cell; what runner transitioned at b?
            term_runners = [r for b_bd, r in boundaries if b_bd == b]
            # Classify: z=0 event or t-transition?
            term_type_list = []
            for r in term_runners:
                z = z_e_val(r, b, L)
                if z == 0:
                    term_type_list.append(f"z0(e={r},gcd={math.gcd(r,n)})")
                else:
                    t_before = t_e_val(r, b - 1, L) if b > 0 else -1
                    t_after  = t_e_val(r, b, L)
                    term_type_list.append(f"t_incr(e={r},t:{t_before}->{t_after})")
            # Also categorise by position: start-of-B_div (lower band)?
            if run_start_idx == 0:
                term_type_list.append("lower_band_edge")

            term_events.append({
                "run_start": run_start_b,
                "run_end": run_end_b,
                "run_len": run_len,
                "term_b": b,
                "term_type": ";".join(term_type_list) if term_type_list else "at_B_div_end",
            })
            in_run = False

    if in_run:
        run_end_b = b_status[-1][0]
        run_len   = len(b_status) - run_start_idx
        term_events.append({
            "run_start": run_start_b,
            "run_end": run_end_b,
            "run_len": run_len,
            "term_b": None,
            "term_type": "at_B_div_end",
        })

    # --- Hypothesis checks ---
    cb_viol         = int(max_obstr_fiber > B_div_count - n)        # CB violation
    h1_fail         = int(n_safe_cells < n)                          # H1 fails if safe cells < n
    # H2: max_obstr_run <= min(L/e - 1)
    min_period_minus1 = int(min_period) - 1 if E_non else 0
    h2_fail         = int(max_obstr_fiber > min_period_minus1)
    # H4: max(L/e) <= B_div_count - n + 1
    period_bound_slack = (B_div_count - n + 1) - max_period if E_non else float('inf')
    h4_fail         = int(period_bound_slack < 0)

    return {
        "L": L,
        "k_div": k_div,
        "k_non": k_non,
        "B_div": B_div_count,
        "B_safe": B_safe,
        "x0": x0,
        "max_obstr_fiber_run": max_obstr_fiber,
        "max_obstr_cell_run": max_obstr_cells,
        "n_safe_cells": n_safe_cells,
        "n_obstr_cells": n_obstr_cells,
        "min_period": int(min_period) if E_non else 0,
        "max_period": int(max_period) if E_non else 0,
        "period_bound_slack": int(period_bound_slack) if period_bound_slack != float('inf') else 9999,
        "cb_violation": cb_viol,
        "h1_fail": h1_fail,
        "h2_fail": h2_fail,
        "h4_fail": h4_fail,
        "tight_cb": int(max_obstr_fiber == B_div_count - n and B_div_count > n),
        "cells": cells,
        "term_events": term_events,
    }


# ---------------------------------------------------------------------------
# Block processor
# ---------------------------------------------------------------------------

def process_block(
    block_label: str, tuples_iter, n: int,
    rows: list[dict], tight_cell_rows: list[dict],
    term_rows: list[dict], summary_parts: list[str],
    phi_n: int
):
    counts = {
        "total": 0, "cb_viol": 0, "h1_fail": 0, "h2_fail": 0,
        "h4_fail": 0, "tight_cb": 0
    }
    mins: dict[str, tuple] = {}

    def upd(key, val, ref):
        if key not in mins or val < mins[key][0]:
            mins[key] = (val, ref)
    def maxupd(key, val, ref):
        if key not in mins or val > mins[key][0]:
            mins[key] = (val, ref)

    for E in tuples_iter:
        if math.gcd(*E) != 1:
            continue
        if not any(e % n == 0 for e in E):
            continue
        L = math.lcm(*E)
        if L == n:
            continue   # canonical case, skip (already proved)

        counts["total"] += 1
        t = analyze_event_path(E, n)
        if t is None:
            counts["total"] -= 1
            continue

        if t["cb_violation"]:
            counts["cb_viol"] += 1
        if t["h1_fail"]:
            counts["h1_fail"] += 1
        if t["h2_fail"]:
            counts["h2_fail"] += 1
        if t["h4_fail"]:
            counts["h4_fail"] += 1
        if t["tight_cb"]:
            counts["tight_cb"] += 1

        e_str = " ".join(map(str, E))
        upd("B_safe", t["B_safe"], e_str)
        upd("n_safe_cells", t["n_safe_cells"], e_str)
        upd("period_bound_slack", t["period_bound_slack"], e_str)
        maxupd("max_obstr_fiber_run", t["max_obstr_fiber_run"], e_str)
        maxupd("max_obstr_cell_run", t["max_obstr_cell_run"], e_str)

        row = {
            "block": block_label, "n": n, "phi_n": phi_n, "e_tuple": e_str,
            "L": t["L"], "k_div": t["k_div"], "k_non": t["k_non"],
            "B_div": t["B_div"], "B_safe": t["B_safe"], "x0": t["x0"],
            "max_obstr_fiber_run": t["max_obstr_fiber_run"],
            "max_obstr_cell_run": t["max_obstr_cell_run"],
            "n_safe_cells": t["n_safe_cells"],
            "n_obstr_cells": t["n_obstr_cells"],
            "min_period": t["min_period"],
            "max_period": t["max_period"],
            "period_bound_slack": t["period_bound_slack"],
            "cb_violation": t["cb_violation"],
            "h1_fail": t["h1_fail"],
            "h2_fail": t["h2_fail"],
            "h4_fail": t["h4_fail"],
            "tight_cb": t["tight_cb"],
        }
        rows.append(row)

        # Tight-case cell sequences
        if t["tight_cb"]:
            for ci, cell in enumerate(t["cells"]):
                sig_str = "; ".join(f"e{e}:(t={v[0]},z={v[1]})" for e, v in sorted(cell["sig"].items()))
                tight_cell_rows.append({
                    "block": block_label, "n": n, "e_tuple": e_str, "L": t["L"],
                    "cell_idx": ci,
                    "b_start": cell["b_start"], "b_end": cell["b_end"],
                    "cell_len": cell["cell_len"],
                    "safe": int(cell["safe"]),
                    "delta": cell["delta"],
                    "signature": sig_str,
                    "trans_runners": str(cell["trans_runners"]),
                })

        # Termination events for obstructed runs
        for te in t["term_events"]:
            term_rows.append({
                "block": block_label, "n": n, "e_tuple": e_str, "L": t["L"],
                "run_len": te["run_len"],
                "term_b": te["term_b"],
                "term_type": te["term_type"],
                "is_tight": t["tight_cb"],
            })

    # Summary for block
    summary_parts.append(f"\n### {block_label} (n={n}, phi={phi_n})")
    summary_parts.append(f"- Tuples processed (L>n): {counts['total']}")
    summary_parts.append(f"- CB violations (max_obstr_run > B_div−n):  {counts['cb_viol']}")
    summary_parts.append(f"- H1 failures (n_safe_cells < n):           {counts['h1_fail']}")
    summary_parts.append(f"- H2 failures (max_obstr > min_period−1):   {counts['h2_fail']}")
    summary_parts.append(f"- H4 failures (period_bound_slack < 0):     {counts['h4_fail']}")
    summary_parts.append(f"- Tight CB cases (max_obstr_run = B_div−n): {counts['tight_cb']}")
    if "B_safe" in mins:
        summary_parts.append(f"- min B_safe:              {mins['B_safe'][0]}  at E={mins['B_safe'][1]}")
    if "n_safe_cells" in mins:
        summary_parts.append(f"- min n_safe_cells:        {mins['n_safe_cells'][0]}  at E={mins['n_safe_cells'][1]}")
    if "period_bound_slack" in mins:
        summary_parts.append(f"- min period_bound_slack:  {mins['period_bound_slack'][0]}  at E={mins['period_bound_slack'][1]}")
    if "max_obstr_fiber_run" in mins:
        summary_parts.append(f"- max max_obstr_fiber_run: {mins['max_obstr_fiber_run'][0]}  at E={mins['max_obstr_fiber_run'][1]}")
    if "max_obstr_cell_run" in mins:
        summary_parts.append(f"- max max_obstr_cell_run:  {mins['max_obstr_cell_run'][0]}  at E={mins['max_obstr_cell_run'][1]}")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    random.seed(42)
    rows: list[dict] = []
    tight_cell_rows: list[dict] = []
    term_rows: list[dict] = []
    summary_parts: list[str] = []

    summary_parts.append("# Gap 4 / S3 — Event-Cell Path Diagnostic (v1)")
    summary_parts.append("")
    summary_parts.append("## Conjecture Tested")
    summary_parts.append("**Complementarity Bound (CB):** max_obstr_run ≤ B_div − n for all L>n tuples.")
    summary_parts.append("")
    summary_parts.append("## Hypotheses")
    summary_parts.append("- H1: n_safe_cells ≥ n (L>n tuples)")
    summary_parts.append("- H2: max_obstr_run ≤ min(L/e − 1 : e ∈ E_non)")
    summary_parts.append("- H4: period_bound_slack = (B_div − n + 1) − max(L/e) ≥ 0")
    summary_parts.append("")

    # Exhaustive composite
    summary_parts.append("## Exhaustive Results")
    for n, max_e in sorted(MAX_E_EXH.items()):
        phi_n = euler_phi(n)
        label = f"exhaustive_composite_n{n}"
        E_iter = (E for E in product(range(1, max_e + 1), repeat=n - 1)
                  if math.lcm(*E) <= L_CAP_EXH)
        process_block(label, E_iter, n, rows, tight_cell_rows, term_rows, summary_parts, phi_n)

    # Exhaustive prime (comparison)
    for n, max_e in sorted(MAX_E_EXH_PRIME.items()):
        phi_n = euler_phi(n)
        label = f"exhaustive_prime_n{n}"
        E_iter = (E for E in product(range(1, max_e + 1), repeat=n - 1)
                  if math.lcm(*E) <= L_CAP_EXH)
        process_block(label, E_iter, n, rows, tight_cell_rows, term_rows, summary_parts, phi_n)

    # Random stress
    summary_parts.append("\n## Random Stress Results")
    for n, max_e, target in RANDOM_CFG:
        phi_n = euler_phi(n)
        label = f"random_n{n}"
        kept = [0]

        def gen(n=n, max_e=max_e, target=target, kept=kept):
            tries = 0
            while kept[0] < target and tries < target * 200:
                tries += 1
                E = tuple(random.randint(1, max_e) for _ in range(n - 1))
                if math.gcd(*E) != 1:
                    continue
                if not any(e % n == 0 for e in E):
                    continue
                L = math.lcm(*E)
                if L > L_CAP_RANDOM or L == n:
                    continue
                kept[0] += 1
                yield E

        process_block(label, gen(), n, rows, tight_cell_rows, term_rows, summary_parts, phi_n)

    # --- Global summary ---
    summary_parts.append("\n## Global Summary")
    total = len(rows)
    cb_viols  = sum(r["cb_violation"] for r in rows)
    h1_fails  = sum(r["h1_fail"] for r in rows)
    h2_fails  = sum(r["h2_fail"] for r in rows)
    h4_fails  = sum(r["h4_fail"] for r in rows)
    tight_cbs = sum(r["tight_cb"] for r in rows)

    summary_parts.append(f"- Total L>n tuples: {total}")
    summary_parts.append(f"- CB violations:    {cb_viols}")
    summary_parts.append(f"- H1 failures:      {h1_fails}")
    summary_parts.append(f"- H2 failures:      {h2_fails}")
    summary_parts.append(f"- H4 failures:      {h4_fails}")
    summary_parts.append(f"- Tight CB cases:   {tight_cbs}")
    summary_parts.append("")

    # Termination type census
    if term_rows:
        from collections import Counter
        type_ctr: Counter = Counter()
        for tr in term_rows:
            # Simplify type for census
            t_str = tr["term_type"]
            if "z0" in t_str:
                key = "z0_event"
            elif "t_incr" in t_str:
                key = "t_increment"
            elif "lower_band_edge" in t_str:
                key = "lower_band_edge"
            elif t_str == "at_B_div_end":
                key = "at_B_div_end"
            else:
                key = "other:" + t_str[:30]
            type_ctr[key] += 1
        summary_parts.append("### Obstructed-run termination types")
        for k, v in type_ctr.most_common():
            summary_parts.append(f"  - {k}: {v} ({100*v/len(term_rows):.1f}%)")
        summary_parts.append("")

    # n_safe_cells distribution
    if rows:
        safe_cell_counts = [r["n_safe_cells"] for r in rows]
        summary_parts.append("### n_safe_cells distribution")
        for n_val in sorted(set(r["n"] for r in rows)):
            subset = [r["n_safe_cells"] for r in rows if r["n"] == n_val]
            if subset:
                summary_parts.append(
                    f"  n={n_val}: min={min(subset)}, max={max(subset)}, "
                    f"mean={sum(subset)/len(subset):.1f}, "
                    f"#(< n)={sum(1 for v in subset if v < n_val)}"
                )
        summary_parts.append("")

    # period_bound_slack distribution
    if rows:
        pbs = [r["period_bound_slack"] for r in rows]
        summary_parts.append("### period_bound_slack distribution")
        summary_parts.append(f"  min={min(pbs)}, max={max(pbs)}, mean={sum(pbs)/len(pbs):.1f}")
        summary_parts.append(f"  negative count: {sum(1 for v in pbs if v < 0)}")
        summary_parts.append("")

    # Tight CB case details
    tight_rows = [r for r in rows if r["tight_cb"]]
    if tight_rows:
        summary_parts.append("### Tight CB cases (max_obstr_run = B_div−n)")
        for r in tight_rows[:20]:
            summary_parts.append(
                f"  n={r['n']}, E={r['e_tuple']}, L={r['L']}, "
                f"B_div={r['B_div']}, B_safe={r['B_safe']}, "
                f"max_obstr_run={r['max_obstr_fiber_run']}, "
                f"n_safe_cells={r['n_safe_cells']}, min_period={r['min_period']}"
            )
        if len(tight_rows) > 20:
            summary_parts.append(f"  ... ({len(tight_rows)} tight cases total)")

    # --- Write outputs ---
    if rows:
        with open(OUT_ROWS, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=[k for k in rows[0] if k not in ("cells", "term_events")])
            w.writeheader()
            w.writerows(rows)
        print(f"wrote: {OUT_ROWS}  ({len(rows)} rows)")

    if tight_cell_rows:
        with open(OUT_TIGHT, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(tight_cell_rows[0].keys()))
            w.writeheader()
            w.writerows(tight_cell_rows)
        print(f"wrote: {OUT_TIGHT}  ({len(tight_cell_rows)} rows)")

    if term_rows:
        with open(OUT_TERM, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(term_rows[0].keys()))
            w.writeheader()
            w.writerows(term_rows)
        print(f"wrote: {OUT_TERM}  ({len(term_rows)} rows)")

    with open(OUT_SUM, "w") as f:
        f.write("\n".join(summary_parts) + "\n")
    print(f"wrote: {OUT_SUM}")


if __name__ == "__main__":
    main()
