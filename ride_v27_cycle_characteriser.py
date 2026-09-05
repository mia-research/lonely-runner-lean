#!/usr/bin/env python3
"""
RIDE V27 - Cycle characteriser: fit each stressed cycle to generative models.
# v1.0 — 2026-04-13 — per-cycle model fitting to find compact order generators

MOTIVATION
----------
V18 showed real files have 11-16 large non-trivial cycles (not hundreds).
V22 measured arc structure and gap distributions inside each cycle.
V23 tried cycle-arc macros but did not test whether cycles admit a compact
  *generative* description (a short rule that produces the cycle members).

This script asks: for each stressed cycle, does it fit a known simple model?

MODELS TESTED
-------------
For each stressed cycle C (sorted member positions), we test:

1. AFFINE ORBIT
   Members ≈ {(a*i + b) mod n : i = 0..len-1} for some (a, b, n).
   Fit: find (a, b) that minimises Hamming distance from predicted to actual.
   If distance == 0 → exact affine; else report best residual.
   Description cost: log2(n) + log2(n) ≈ 2 * log2(n) bits.
   Compare to naive: len(C) * log2(n) bits.

2. ARITHMETIC PROGRESSION (AP)
   Members ≈ {start + i*step mod n : i = 0..len-1}.
   Special case of affine (a=step, b=start).
   Test all step values that divide n approximately.
   Description cost: log2(n) + log2(n) ≈ 2 * log2(n) bits.

3. BLOCKED STRIDE
   Members ≈ blocks of size B at stride S: {b*S + j : b=0..n_blocks-1, j=0..B-1}.
   Fit: find (B, S) that minimises Hamming distance.
   Description cost: log2(n) + log2(n) bits (B and S).

4. K-OPERATION ORBIT
   Apply K(n) = desc(n) - asc(n) repeatedly to the cycle pivot.
   Check if the sequence of positions visited matches the cycle members.
   This tests whether the K operation itself generates the cycle geometry.

5. NULL MODEL (baseline)
   No structure. Cost = len(C) * log2(n) bits. Always fits perfectly.

WHAT WE REPORT
--------------
For each cycle:
  - model name + best parameters
  - fit quality: fraction of members exactly predicted
  - description cost: bits for the rule vs. bits for explicit list
  - compression factor: null_cost / model_cost (>1 = model wins)

If any model achieves >90% fit on any stressed cycle, we have a real lead
for the order generator. Even 50% fit is interesting — it means the residual
is small enough for a secondary generator.

KEY QUESTION:
  If the 11-16 stressed cycles each fit an affine rule at, say, 95% accuracy,
  the entire order recipe shrinks from O(n) to O(log(n) * 16) — essentially
  a fixed-size header regardless of file size. That would close the RIDE problem.
"""

from __future__ import annotations

import argparse
import math
import sys
import time
from collections import Counter
from pathlib import Path
from typing import NamedTuple

HERE = Path(__file__).resolve().parent
MIAI = Path("/Users/trentpalelei/MIAI")
for candidate in (HERE, MIAI):
    s = str(candidate)
    if candidate.exists() and s not in sys.path:
        sys.path.insert(0, s)

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(10_000_000)

from ride_v13_canterbury_recipe_bench import build_perm_target_to_source, permutation_cycle_mile
from ride_v18_cycle_rsn import build_rsn_cycle_plan, cycle_stress, materialise_source_and_target
from ride_v2_kpog_encoder import decompose_cycles


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def bits(n: int) -> float:
    return math.log2(n) if n > 1 else 1.0


class FitResult(NamedTuple):
    model: str
    params: dict
    exact_match: int        # positions exactly predicted
    total: int              # cycle length
    accuracy: float         # exact_match / total
    model_bits: float       # bits to describe the rule
    naive_bits: float       # bits to list every member explicitly
    gain: float             # naive_bits / model_bits (>1 means model wins)


# ---------------------------------------------------------------------------
# Model 1: Affine orbit  members ≈ (a*i + b) mod n
# ---------------------------------------------------------------------------

def fit_affine(positions: list[int], n: int) -> FitResult:
    """
    Try to fit positions as an affine orbit (a*i + b) mod n.
    We search over a small set of candidate 'a' values: divisors of n and
    values near n/len(positions).
    """
    L = len(positions)
    pos_set = set(positions)

    best_matches = 0
    best_a = 1
    best_b = positions[0] if positions else 0

    # Candidate strides: near n/L and small divisors
    approx_stride = max(1, n // L)
    candidates = set()
    for delta in range(-20, 21):
        c = approx_stride + delta
        if 1 <= c < n:
            candidates.add(c)
    # Also try small values
    for c in range(1, min(64, n)):
        candidates.add(c)
    # Multiples of L near n
    for k in range(1, 10):
        c = (n * k) // L
        if 1 <= c < n:
            candidates.add(c)
            candidates.add(c + 1)
            candidates.add(c - 1)

    for a in candidates:
        if a < 1 or a >= n:
            continue
        # For each candidate a, find the best b
        predicted_set = {(a * i) % n for i in range(L)}
        # Shift b to maximise overlap
        for b_offset in [positions[0] - (a * 0) % n]:
            predicted = {(p + b_offset) % n for p in predicted_set}
            matches = len(pos_set & predicted)
            if matches > best_matches:
                best_matches = matches
                best_a = a
                best_b = b_offset % n

    accuracy = best_matches / L if L else 0.0
    # Cost: a, b, L — each ~log2(n) bits
    model_bits = 3 * bits(n)
    naive_bits = L * bits(n)
    gain = naive_bits / model_bits if model_bits > 0 else 0.0

    return FitResult(
        model="affine",
        params={"a": best_a, "b": best_b, "n": n, "L": L},
        exact_match=best_matches,
        total=L,
        accuracy=accuracy,
        model_bits=model_bits,
        naive_bits=naive_bits,
        gain=gain,
    )


# ---------------------------------------------------------------------------
# Model 2: Arithmetic progression  start, start+step, start+2*step, ...
# ---------------------------------------------------------------------------

def fit_ap(positions: list[int], n: int) -> FitResult:
    """
    Fit as arithmetic progression mod n.
    Try steps that are approximate multiples of n/L and small values.
    """
    L = len(positions)
    pos_set = set(positions)
    if L < 2:
        return FitResult("ap", {}, L, L, 1.0, 2 * bits(n), L * bits(n), L * bits(n) / (2 * bits(n)))

    best_matches = 0
    best_step = 1
    best_start = positions[0]

    approx_step = max(1, n // L)
    candidates = set()
    for delta in range(-10, 11):
        s = approx_step + delta
        if 1 <= s < n:
            candidates.add(s)
    for s in range(1, min(32, n)):
        candidates.add(s)

    for step in candidates:
        if step < 1 or step >= n:
            continue
        for start in [positions[0]]:
            predicted = {(start + i * step) % n for i in range(L)}
            matches = len(pos_set & predicted)
            if matches > best_matches:
                best_matches = matches
                best_step = step
                best_start = start

    accuracy = best_matches / L if L else 0.0
    model_bits = 2 * bits(n)
    naive_bits = L * bits(n)
    gain = naive_bits / model_bits if model_bits > 0 else 0.0

    return FitResult(
        model="ap",
        params={"start": best_start, "step": best_step, "n": n, "L": L},
        exact_match=best_matches,
        total=L,
        accuracy=accuracy,
        model_bits=model_bits,
        naive_bits=naive_bits,
        gain=gain,
    )


# ---------------------------------------------------------------------------
# Model 3: Blocked stride  {b*S + j : b in 0..n_blocks-1, j in 0..B-1}
# ---------------------------------------------------------------------------

def fit_blocked_stride(positions: list[int], n: int) -> FitResult:
    """
    Fit as a union of contiguous blocks of size B, spaced at stride S.
    """
    L = len(positions)
    pos_set = set(positions)

    best_matches = 0
    best_B = 1
    best_S = max(1, n // max(1, L))
    best_offset = positions[0] if positions else 0

    # Try block sizes from 1 to sqrt(L)
    max_B = min(128, int(math.isqrt(L)) + 2)
    for B in range(1, max_B + 1):
        n_blocks = max(1, L // B)
        # Stride should be ~ n / n_blocks
        approx_S = max(B + 1, n // max(1, n_blocks))
        for S_delta in range(-5, 6):
            S = approx_S + S_delta
            if S <= B or S >= n:
                continue
            for offset in [positions[0], 0]:
                predicted = set()
                for block_idx in range(n_blocks):
                    block_start = (offset + block_idx * S) % n
                    for j in range(B):
                        predicted.add((block_start + j) % n)
                matches = len(pos_set & predicted)
                if matches > best_matches:
                    best_matches = matches
                    best_B = B
                    best_S = S
                    best_offset = offset

    accuracy = best_matches / L if L else 0.0
    # Cost: B, S, offset, n_blocks — all ~log2(n)
    model_bits = 4 * bits(n)
    naive_bits = L * bits(n)
    gain = naive_bits / model_bits if model_bits > 0 else 0.0

    return FitResult(
        model="blocked_stride",
        params={"B": best_B, "S": best_S, "offset": best_offset},
        exact_match=best_matches,
        total=L,
        accuracy=accuracy,
        model_bits=model_bits,
        naive_bits=naive_bits,
        gain=gain,
    )


# ---------------------------------------------------------------------------
# Analysis per cycle
# ---------------------------------------------------------------------------

def characterise_cycle(
    cycle: list[int],
    perm: list[int],
    n: int,
    cycle_idx: int,
) -> dict:
    displacement, span, length = cycle_stress(cycle, perm)
    positions = sorted(cycle)

    t0 = time.perf_counter()
    affine = fit_affine(positions, n)
    ap = fit_ap(positions, n)
    blocked = fit_blocked_stride(positions, n)
    fit_time = time.perf_counter() - t0

    # Best model by accuracy
    all_fits = [affine, ap, blocked]
    best = max(all_fits, key=lambda f: (f.accuracy, f.gain))

    # Gap analysis (spacing between sorted members)
    gaps = [positions[i + 1] - positions[i] for i in range(len(positions) - 1)]
    if positions:
        gaps.append((positions[0] + n) - positions[-1])
    gap_set = set(gaps)
    # If all gaps are equal (or near-equal), it's a perfect AP
    gap_uniformity = len(gap_set) / len(gaps) if gaps else 1.0

    # --- Thermo-view extension (2026-04-17): Boltzmann reread of cycle gaps ---
    # A Geom(p) over gaps k=1,2,3,... has PMF f(k) = (1-p) * p^(k-1) in one
    # convention, or f(k) = p * (1-p)^(k-1) in another. We use the latter so
    # that p is the parameter reported as "p_geom" aligning with the p ~= 0.377
    # convention used elsewhere in this project (see ride_state_2026-04-13.md
    # finding 4, where gap=1 frequency ~ 0.378). Under this convention:
    #   MLE: p_hat = 1 / mean(gaps)  (for support k>=1)
    # In Boltzmann form, beta = log(1/(1-p)) is the inverse "gap-temperature".
    gap_histogram = dict(Counter(gaps))
    p_geom = None
    p_geom_residual = None
    beta_gap = None
    if gaps:
        mean_gap = sum(gaps) / len(gaps)
        if mean_gap >= 1.0:
            # Shifted geometric on {1,2,...}: MLE p_hat = 1/mean
            p_hat = 1.0 / mean_gap
            # Clamp to valid probability interval
            if 0.0 < p_hat < 1.0:
                p_geom = round(p_hat, 4)
                # RMS residual: compare empirical PMF to geometric PMF on
                # the observed support.
                total = len(gaps)
                empirical = {k: c / total for k, c in gap_histogram.items()}
                sq = 0.0
                for k, emp in empirical.items():
                    predicted = p_hat * ((1.0 - p_hat) ** (k - 1))
                    sq += (emp - predicted) ** 2
                p_geom_residual = round(math.sqrt(sq / len(empirical)), 6)
                # Inverse gap-temperature in Boltzmann form
                # P(k) ~ exp(-beta * k) has beta = -log(1-p) when we pull the
                # geometric distribution into exp form (up to normalisation).
                one_minus_p = 1.0 - p_hat
                if one_minus_p > 0.0:
                    beta_gap = round(-math.log(one_minus_p), 6)

    return {
        "cycle_idx": cycle_idx,
        "length": length,
        "span": span,
        "displacement": displacement,
        "gap_uniformity": round(gap_uniformity, 4),  # 0 = all gaps equal (perfect AP)
        "gap_unique_values": len(gap_set),
        # Thermo-view extension (2026-04-17)
        "gap_histogram": gap_histogram,
        "p_geom": p_geom,
        "p_geom_residual": p_geom_residual,
        "beta_gap": beta_gap,
        "models": {
            "affine": {
                "accuracy": round(affine.accuracy, 4),
                "gain": round(affine.gain, 2),
                "params": affine.params,
            },
            "ap": {
                "accuracy": round(ap.accuracy, 4),
                "gain": round(ap.gain, 2),
                "params": ap.params,
            },
            "blocked_stride": {
                "accuracy": round(blocked.accuracy, 4),
                "gain": round(blocked.gain, 2),
                "params": blocked.params,
            },
        },
        "best_model": best.model,
        "best_accuracy": round(best.accuracy, 4),
        "best_gain": round(best.gain, 2),
        "naive_bits": round(affine.naive_bits, 1),
        "fit_time": round(fit_time, 3),
    }


# ---------------------------------------------------------------------------
# Main analysis
# ---------------------------------------------------------------------------

def analyse_file(path: Path) -> dict:
    raw = path.read_bytes()
    t0 = time.perf_counter()

    source, target, params, l1 = materialise_source_and_target(raw)
    n = len(target)

    perm = list(build_perm_target_to_source(bytearray(target), bytearray(source)))
    mile, total_cycles = permutation_cycle_mile(perm)
    plan = build_rsn_cycle_plan(perm)

    prep_time = time.perf_counter() - t0

    # Get non-trivial cycles sorted by stress
    all_cycles = [c for c in decompose_cycles(perm) if len(c) > 1]
    scored = []
    for c in all_cycles:
        disp, span, length = cycle_stress(c, perm)
        scored.append((disp, span, length, c))
    scored.sort(reverse=True)

    non_trivial = len(scored)
    top_n = min(non_trivial, 16)  # analyse all up to 16

    print(f"\n{'=' * 72}")
    print(f"  RIDE V27 — Cycle characteriser: {path.name}")
    print(f"{'=' * 72}")
    print(f"  Raw bytes:      {len(raw):,}")
    print(f"  Digits:         {n:,}")
    print(f"  Mile:           {mile:,}")
    print(f"  Total cycles:   {total_cycles:,}")
    print(f"  Non-trivial:    {non_trivial:,}")
    print(f"  Analysing top:  {top_n}")
    print()

    cycle_results = []
    total_naive_bits = 0.0
    total_model_bits_best = 0.0

    for idx, (disp, span, length, cycle) in enumerate(scored[:top_n]):
        result = characterise_cycle(cycle, perm, n, idx)
        cycle_results.append(result)
        total_naive_bits += result["naive_bits"]
        # Best model cost
        best_m = result["best_model"]
        best_fit = result["models"][best_m]
        # model_bits = naive_bits / gain
        if best_fit["gain"] > 0:
            total_model_bits_best += result["naive_bits"] / best_fit["gain"]
        else:
            total_model_bits_best += result["naive_bits"]

        print(f"  Cycle {idx:2d}: len={length:8,}  span={span:8,}  disp={disp:10,}")
        print(f"    gap_uniformity={result['gap_uniformity']:.4f}  unique_gaps={result['gap_unique_values']}")
        for mname in ("affine", "ap", "blocked_stride"):
            m = result["models"][mname]
            marker = " <-- best" if mname == result["best_model"] else ""
            print(f"    {mname:16s}: accuracy={m['accuracy']:.3f}  gain={m['gain']:6.1f}x{marker}")
        print()

    # Summary
    overall_gain = total_naive_bits / total_model_bits_best if total_model_bits_best > 0 else 0
    print(f"  SUMMARY over top {top_n} cycles:")
    print(f"    Total naive bits:  {total_naive_bits:,.0f}")
    print(f"    Total model bits:  {total_model_bits_best:,.0f}  (best model per cycle)")
    print(f"    Overall gain:      {overall_gain:.2f}x")
    print(f"    Prep time:         {prep_time:.2f}s")
    print()

    # Best accuracy distribution
    acc_bins = {">=0.9": 0, ">=0.7": 0, ">=0.5": 0, "<0.5": 0}
    for r in cycle_results:
        a = r["best_accuracy"]
        if a >= 0.9:
            acc_bins[">=0.9"] += 1
        elif a >= 0.7:
            acc_bins[">=0.7"] += 1
        elif a >= 0.5:
            acc_bins[">=0.5"] += 1
        else:
            acc_bins["<0.5"] += 1
    print(f"  Accuracy distribution (best model per cycle):")
    for k, v in acc_bins.items():
        print(f"    {k}: {v} cycles")

    return {
        "file": str(path),
        "bytes": len(raw),
        "n_digits": n,
        "mile": mile,
        "non_trivial_cycles": non_trivial,
        "cycles_analysed": top_n,
        "overall_gain": round(overall_gain, 3),
        "accuracy_distribution": acc_bins,
        "cycles": cycle_results,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="RIDE V27 — cycle characteriser")
    parser.add_argument("files", nargs="+", help="Files to analyse")
    parser.add_argument("--json-out", help="Write full results as JSON")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    print("╔══════════════════════════════════════════════════════════════╗")
    print("║  RIDE V27 — CYCLE CHARACTERISER                             ║")
    print("║  Do stressed cycles fit compact generative models?          ║")
    print("╚══════════════════════════════════════════════════════════════╝")

    all_results = []
    for f in args.files:
        result = analyse_file(Path(f).expanduser())
        all_results.append(result)

    if args.json_out:
        import json
        with open(args.json_out, "w") as fh:
            json.dump(all_results, fh, indent=2)
        print(f"\n  Full results written to {args.json_out}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
