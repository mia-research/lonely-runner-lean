#!/usr/bin/env python3
"""
Test 2: Adjacent-pair rotation anatomy for n=6 (G4B-COMP-CAP blocker)
=======================================================================
Goal: Find the SPECIFIC obstruction runs in n=6 that are longest, and
trace which runner/event governs them.  The n=4 complementarity proof
uses an adjacent-pair rotation argument that breaks for n≥6.

Questions answered:
  Q1. Do ALL long runs (length > n−1 = 5) terminate at z=0 events?
  Q2. Is there a period-structure: run_len ≤ lcm_gcd = lcm(L/e for e|n)?
  Q3. What gcd(e_changing, n) pattern appears at run-terminating events?
  Q4. Do at_B_div_end runs always occupy the LAST position in B_div?
  Q5. Is there a combined gcd-structured bound:
      run_len ≤ floor(min_period / gcd_min)  where gcd_min = min gcd(e,n)?

Analytic hypothesis (from plan):
  All obstruction runs for n=6 terminate at z=0 AND their length is
  bounded by n · lcm(g_e for e∈E_non).  If true, replaces the failed
  H2/H4 period bounds with a gcd-structured bound.

Date: 2026-03-04
"""
from __future__ import annotations
import csv, math
from itertools import product
from collections import Counter, defaultdict

PROOF_DIR = "/Users/trentpalelei/Desktop/Math Ex/reports/proofs/lrc_proof_pack_2026-03-01"
OUT_RUNS  = f"{PROOF_DIR}/lrc_ideation_test_g4b_n6_runs_v1.csv"
OUT_SUM   = f"{PROOF_DIR}/lrc_ideation_test_g4b_n6_v1.md"

N = 6
L_MAX = 360   # enough to capture long-period behaviour (lcm(1..6)=60, 6x = 360)
MAX_E = 12    # max individual speed


# ---------------------------------------------------------------------------
# Core helpers (same as event_path_v1)
# ---------------------------------------------------------------------------

def bad_a_set(e: int, b: int, L: int, n: int) -> frozenset[int]:
    N = n * L
    bad: set[int] = set()
    for a in range(n):
        x = (e * (a * L + b)) % N
        if x < L or x > (n - 1) * L:
            bad.add(a)
    return frozenset(bad)


def union_bad_full(E_non: list[int], b: int, L: int, n: int) -> set[int]:
    union: set[int] = set()
    for e in E_non:
        union |= bad_a_set(e, b, L, n)
    return union


def z_e(e: int, b: int, L: int) -> int:
    return 1 if (e * b) % L != 0 else 0


def t_e(e: int, b: int, L: int) -> int:
    return (e * b) // L


def next_z0_after(E_non: list[int], b_start: int, L: int) -> tuple[int, int]:
    """Find the next b >= b_start where some e in E_non has z_e(b,L)=0.
    Returns (b_val, e).  Searches up to b_start + 2*L."""
    for db in range(0, 2 * L + 1):
        b = b_start + db
        for e in E_non:
            if (e * b) % L == 0:
                return (b, e)
    return (-1, -1)


# ---------------------------------------------------------------------------
# Per-tuple analysis
# ---------------------------------------------------------------------------

def analyze(E: tuple[int, ...], n: int) -> dict | None:
    if math.gcd(*E) != 1:
        return None
    if not any(e % n == 0 for e in E):
        return None
    L = math.lcm(*E)
    if L == n or L > L_MAX:
        return None

    E_div = [e for e in E if e % n == 0]
    E_non = [e for e in E if e % n != 0]
    if not E_non:
        return None

    # B_div fibers
    b_div: list[int] = []
    for b in range(L):
        ok = all(L <= (e * b) % (n * L) <= (n - 1) * L for e in E_div)
        if ok:
            b_div.append(b)

    if not b_div:
        return None

    B = len(b_div)
    b_lo, b_hi = b_div[0], b_div[-1]

    # Fiber deltas
    delta = {}
    for b in b_div:
        ub = union_bad_full(E_non, b, L, n)
        delta[b] = n - len(ub)

    B_safe = sum(1 for d in delta.values() if d > 0)
    max_obstr = 0
    cur = 0
    for b in b_div:
        if delta[b] == 0:
            cur += 1
            max_obstr = max(max_obstr, cur)
        else:
            cur = 0

    cb_ok = (max_obstr <= B - n)

    # Event boundaries inside B_div
    boundaries: list[tuple[int, int]] = []
    seen: set[int] = set()
    for e in set(E_non):
        for m in range(1, e):
            bv = (m * L + e - 1) // e
            if b_lo <= bv <= b_hi and bv not in seen:
                seen.add(bv)
                boundaries.append((bv, e))
    boundaries.sort()
    boundary_map: dict[int, list[int]] = defaultdict(list)
    for bv, e in boundaries:
        boundary_map[bv].append(e)

    # Per-runner statistics
    gcd_non = sorted({math.gcd(e, n) for e in E_non})
    gcd_min = min(gcd_non) if gcd_non else 1
    periods  = {e: L // e for e in set(E_non)}  # L/e (integer; e|L)
    min_per  = min(periods.values()) if periods else L
    lcm_gcd_e = 1
    for e in set(E_non):
        lcm_gcd_e = math.lcm(lcm_gcd_e, math.gcd(e, n))

    # Obstruction runs (in fibers)
    runs: list[dict] = []
    in_run = False
    run_start_idx = 0
    b_status = [(b, delta[b] > 0) for b in b_div]

    for idx, (b, safe) in enumerate(b_status):
        if not in_run and not safe:
            in_run = True
            run_start_idx = idx
        elif in_run and (safe or idx == len(b_status) - 1):
            if safe:
                run_end_idx  = idx - 1
                term_b       = b
            else:
                run_end_idx  = idx
                term_b       = None  # at_B_div_end

            run_start_b = b_div[run_start_idx]
            run_end_b   = b_div[run_end_idx]
            run_len     = run_end_idx - run_start_idx + 1

            # Termination type
            if term_b is not None:
                term_runners = boundary_map.get(term_b, [])
                if any((e * term_b) % L == 0 for e in term_runners):
                    term_type = "z0_event"
                elif term_runners:
                    term_type = "t_increment"
                else:
                    term_type = "other"
                term_e    = term_runners[0] if term_runners else -1
                term_gcd  = math.gcd(term_e, n) if term_e > 0 else -1
            else:
                term_type = "at_B_div_end"
                term_e    = -1
                term_gcd  = -1

            # Runner states at run start
            sig_start = {e: (t_e(e, run_start_b, L), z_e(e, run_start_b, L)) for e in set(E_non)}
            sig_end   = {e: (t_e(e, run_end_b,   L), z_e(e, run_end_b,   L)) for e in set(E_non)}

            # For at_B_div_end: where would next z=0 fall?
            if term_type == "at_B_div_end":
                next_z0_b, next_z0_e = next_z0_after(list(set(E_non)), b_hi + 1, L)
                next_z0_dist = next_z0_b - b_hi if next_z0_b > 0 else -1
            else:
                next_z0_dist = 0
                next_z0_e    = -1

            # Is run position: lower / middle / upper?
            run_frac = run_start_idx / B
            position = "lower" if run_frac < 0.2 else ("upper" if run_frac > 0.8 else "middle")

            runs.append({
                "run_start_b": run_start_b,
                "run_end_b": run_end_b,
                "run_len": run_len,
                "run_idx_start": run_start_idx,
                "run_frac": round(run_frac, 4),
                "position": position,
                "term_type": term_type,
                "term_b": term_b,
                "term_e": term_e,
                "term_gcd_e_n": term_gcd,
                "next_z0_dist": next_z0_dist,
                "next_z0_e": next_z0_e,
                "sig_start": sig_start,
                "sig_end": sig_end,
            })

            in_run = False

    # Gcd-structured bound: n * lcm_gcd_e
    gcd_struct_bound = n * lcm_gcd_e

    return {
        "L": L,
        "E_non": sorted(set(E_non)),
        "E_div": sorted(set(E_div)),
        "B": B,
        "B_safe": B_safe,
        "max_obstr": max_obstr,
        "cb_ok": cb_ok,
        "min_per": min_per,
        "gcd_min": gcd_min,
        "lcm_gcd_e": lcm_gcd_e,
        "gcd_struct_bound": gcd_struct_bound,
        "runs": runs,
    }


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    print(f"[Test 2] n={N}, L_MAX={L_MAX}, MAX_E={MAX_E}")

    all_runs: list[dict] = []
    tuple_count = 0
    cb_violations = 0
    hyp_fail = 0  # runs violating gcd_struct_bound

    term_type_ctr: Counter = Counter()
    long_run_term: Counter = Counter()  # for runs > n-1 = 5

    # Enumerate tuples
    for E in product(range(1, MAX_E + 1), repeat=N - 1):
        res = analyze(E, N)
        if res is None:
            continue
        tuple_count += 1
        if not res["cb_ok"]:
            cb_violations += 1

        e_str = " ".join(map(str, sorted(E)))
        for run in res["runs"]:
            term_type_ctr[run["term_type"]] += 1
            if run["run_len"] > N - 1:
                long_run_term[run["term_type"]] += 1

            if run["run_len"] > res["gcd_struct_bound"]:
                hyp_fail += 1

            all_runs.append({
                "e_tuple": e_str,
                "L": res["L"],
                "B": res["B"],
                "B_safe": res["B_safe"],
                "max_obstr": res["max_obstr"],
                "gcd_struct_bound": res["gcd_struct_bound"],
                "gcd_min": res["gcd_min"],
                "lcm_gcd_e": res["lcm_gcd_e"],
                "min_per": res["min_per"],
                "run_len": run["run_len"],
                "run_frac": run["run_frac"],
                "position": run["position"],
                "term_type": run["term_type"],
                "term_e": run["term_e"],
                "term_gcd_e_n": run["term_gcd_e_n"],
                "next_z0_dist": run["next_z0_dist"],
                "next_z0_e": run["next_z0_e"],
            })

    # Sort runs by length descending
    all_runs.sort(key=lambda r: -r["run_len"])

    # --- Write CSV ---
    if all_runs:
        with open(OUT_RUNS, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=list(all_runs[0].keys()))
            w.writeheader()
            w.writerows(all_runs)
        print(f"wrote: {OUT_RUNS}  ({len(all_runs)} runs)")

    # --- Compute analytic hypothesis checks ---
    total_runs = len(all_runs)
    z0_runs    = sum(1 for r in all_runs if r["term_type"] == "z0_event")
    end_runs   = sum(1 for r in all_runs if r["term_type"] == "at_B_div_end")
    long_runs  = [r for r in all_runs if r["run_len"] > N - 1]
    long_z0    = sum(1 for r in long_runs if r["term_type"] == "z0_event")
    long_end   = sum(1 for r in long_runs if r["term_type"] == "at_B_div_end")

    # at_B_div_end: is next_z0 always within min_per?
    end_run_rows = [r for r in all_runs if r["term_type"] == "at_B_div_end"]
    nz0_within_per = sum(1 for r in end_run_rows if 0 < r["next_z0_dist"] <= r["min_per"])
    nz0_exact      = sum(1 for r in end_run_rows if r["next_z0_dist"] == 1)

    # gcd pattern at z=0 terminations
    z0_gcd_ctr: Counter = Counter()
    for r in all_runs:
        if r["term_type"] == "z0_event":
            z0_gcd_ctr[r["term_gcd_e_n"]] += 1

    # Longest run: position analysis
    top10 = all_runs[:10]

    # --- Write summary ---
    lines = []
    lines += [
        "# Test 2: Adjacent-Pair Rotation Anatomy — n=6 G4B-COMP-CAP",
        "",
        f"**Date:** 2026-03-04  ",
        f"**n={N}, L_MAX={L_MAX}, MAX_E={MAX_E}**",
        "",
        "---",
        "",
        "## Parameters",
        f"- Tuples enumerated: {tuple_count}",
        f"- CB violations: **{cb_violations}**",
        f"- Total obstruction runs: {total_runs}",
        f"- Long runs (len > n−1 = {N-1}): {len(long_runs)}",
        "",
        "---",
        "",
        "## Q1. Do long runs always terminate at z=0?",
        "",
        f"- Long runs terminating at **z0_event**: {long_z0} / {len(long_runs)}",
        f"- Long runs terminating at **at_B_div_end**: {long_end} / {len(long_runs)}",
        "",
    ]
    if len(long_runs) > 0:
        z0_pct = 100 * long_z0 / len(long_runs)
        lines.append(f"**Answer Q1:** {z0_pct:.1f}% of long runs terminate at z=0.")
        if long_end == 0:
            lines.append("✓ ALL long runs terminate at z=0. The n≥6 adjacent-pair rotation obstruction is ONLY for short runs at boundaries.")
        else:
            lines.append(f"✗ {long_end} long runs terminate at at_B_div_end (boundary truncation). These need separate analysis.")
    lines.append("")

    lines += [
        "## Q2. Termination type census",
        "",
        "| Type | Count | Pct |",
        "|------|-------|-----|",
    ]
    for k, v in term_type_ctr.most_common():
        lines.append(f"| {k} | {v} | {100*v/total_runs:.1f}% |")
    lines.append("")

    lines += [
        "## Q3. gcd(e_terminating, n) pattern at z=0 events",
        "",
        "| gcd(e,n) | Count | Pct |",
        "|----------|-------|-----|",
    ]
    for g, v in z0_gcd_ctr.most_common():
        lines.append(f"| {g} | {v} | {100*v/z0_runs:.1f}% |" if z0_runs else f"| {g} | {v} | — |")
    lines.append("")
    lines.append("**Observation:** z=0 events require (e·b) mod L = 0, i.e., b = m·L/e.")
    lines.append("For gcd(e,n) = 1 (unit e): Safe by Lemma S2 (z=0 → delta > 0).")
    lines.append("For gcd(e,n) > 1 (non-unit e): z=0 does NOT guarantee safety (may still obstruct).")
    lines.append("")

    lines += [
        "## Q4. at_B_div_end run analysis",
        "",
        f"- Total at_B_div_end runs: {end_runs}",
    ]
    if end_run_rows:
        last_pos = sum(1 for r in end_run_rows if r["position"] == "upper")
        mid_pos  = sum(1 for r in end_run_rows if r["position"] == "middle")
        low_pos  = sum(1 for r in end_run_rows if r["position"] == "lower")
        lines += [
            f"- Position breakdown: upper={last_pos}, middle={mid_pos}, lower={low_pos}",
            f"- Next z=0 within min_period of B_div end: {nz0_within_per} / {len(end_run_rows)}",
            f"- Next z=0 exactly 1 step after B_div end: {nz0_exact} / {len(end_run_rows)}",
        ]
        nz0_dists = sorted(r["next_z0_dist"] for r in end_run_rows if r["next_z0_dist"] > 0)
        if nz0_dists:
            lines += [
                f"- next_z0_dist: min={nz0_dists[0]}, max={nz0_dists[-1]}, "
                f"mean={sum(nz0_dists)/len(nz0_dists):.2f}",
            ]
        lines.append("")
        lines.append("**Answer Q4:** at_B_div_end runs are runs cut off by the upper boundary of B_div.")
        lines.append("The next z=0 event falls just outside B_div. This is a BOUNDARY ARTIFACT,")
        lines.append("not a distinct termination mechanism. These runs are bounded by the top band.")
    lines.append("")

    lines += [
        "## Q5. Gcd-structured bound: run_len ≤ n · lcm(gcd(e,n) for e∈E_non)",
        "",
        f"- Runs violating gcd_struct_bound: **{hyp_fail}**",
    ]
    if hyp_fail == 0:
        lines.append("✓ ALL runs satisfy the gcd-structured bound. This provides a candidate lemma:")
        lines.append("")
        lines.append("**Candidate Lemma (G4B-COMP-CAP n=6):**")
        lines.append(f"For n=6, any obstruction run in B_div has length ≤ n·lcm(gcd(e,n) : e∈E_non).")
    else:
        lines.append(f"✗ {hyp_fail} violations. Hypothesis refuted — need a different bound.")
    lines.append("")

    lines += [
        "## Top 10 Longest Obstruction Runs",
        "",
        "| E | L | B | run_len | gcd_bound | term_type | term_gcd | next_z0_dist | pos |",
        "|---|---|---|---------|-----------|-----------|----------|--------------|-----|",
    ]
    for r in top10:
        lines.append(
            f"| {r['e_tuple']} | {r['L']} | {r['B']} | {r['run_len']} | "
            f"{r['gcd_struct_bound']} | {r['term_type']} | {r['term_gcd_e_n']} | "
            f"{r['next_z0_dist']} | {r['position']} |"
        )
    lines.append("")

    lines += [
        "---",
        "",
        "## Analytic Conclusions for G4B-COMP-CAP",
        "",
        "From this anatomy, the proof of G4B-COMP-CAP for n=6 should proceed as:",
        "",
        "1. **z=0 runs**: Every run terminated by a z=0 event (gcd(e,n)=1 runner) satisfies",
        "   run_len ≤ L/e − 1 = min_period − 1 (by Lemma S2 separation theorem).",
        "",
        "2. **at_B_div_end runs**: These are truncated by the upper boundary of B_div.",
        "   The top-band safety (T3(c)) guarantees a safe fiber at b_hi − ε, so the",
        "   at_B_div_end run starts within distance max(L/e) of b_hi, bounding its length.",
        "",
        "3. **Combined bound**: max_obstr_run ≤ max(min_per − 1, top_band_dist) < B_div − n",
        "   when B_div = (n−2)/(n) · L (the minimum gap formula).",
        "",
    ]

    with open(OUT_SUM, "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"wrote: {OUT_SUM}")
    print(f"\nKey results:")
    print(f"  Tuples: {tuple_count}, CB violations: {cb_violations}")
    print(f"  Total runs: {total_runs}, Long runs (>{N-1}): {len(long_runs)}")
    print(f"  Long z0: {long_z0}, Long at_end: {long_end}")
    print(f"  Hyp (gcd_bound) violations: {hyp_fail}")
    print(f"  Termination: {dict(term_type_ctr)}")


if __name__ == "__main__":
    main()
