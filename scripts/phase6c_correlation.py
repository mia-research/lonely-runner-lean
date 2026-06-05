"""
Phase 6c — Structural correlation analysis: why LRC-shape avoids adversarial alignment.

Background: Phase 6b showed expected_overlap is a soft separator (misclassifies 18/734
between L_residual and CE), and target_density is too (misclassifies 27).
No single density invariant gives a PERFECT separator.

Hypothesis: LRC-shape forces POSITIVE CORRELATION between bands and targets.
For CE (typically non-LRC-shape), bands and targets can be ADVERSARIALLY arranged
even when expected overlap is high — this is why CE with expected_overlap = 10
can still have N_joint = 0.

Quantitative test:
  correlation_ratio = N_joint / expected_overlap (= 1 means "random", >1 positive
                                                   correlation, <1 negative)

For L_residual: correlation_ratio should be ≈ 1 (random-like).
For CE: correlation_ratio = 0 always (adversarial).

Additional test: compound separator (expected_overlap > T) AND (LRC-shape structure
invariants). Try:
  - kG + kA == n - 1 (LRC-shape cardinality)
  - gcd of speed set
  - vmax bound
  - Phase 4 invariant
"""

import csv
import math
import os


CSV_IN = "/Users/trentpalelei/Desktop/Math Ex/reports/phase6b_density_separator.csv"
CSV_OUT = "/Users/trentpalelei/Desktop/Math Ex/reports/phase6c_correlation.csv"


def load_phase6b_rows():
    rows = []
    with open(CSV_IN, newline="") as f:
        for r in csv.DictReader(f):
            for k in ("n", "p", "kG", "kA", "L_G", "L_A", "nLA", "cIG", "cIA",
                      "res_G_mod_LG", "n_shift_residues_mod_LA",
                      "n_band_betas", "n_band_betas_mod_LA", "n_missed_res_mod_LA",
                      "full_res_classes", "partial_res_classes",
                      "within_res_target_total", "within_res_target_missed",
                      "deficit", "N_joint", "vmax", "pigeon_deficit"):
                if k in r:
                    r[k] = int(r[k])
            for k in ("cover_density", "expected_overlap", "cell_density_product",
                      "band_len_per_cell", "raw_band_coverage", "band_overlap_ratio",
                      "target_density", "coverage_density"):
                if k in r:
                    r[k] = float(r[k])
            rows.append(r)
    return rows


def augment(row):
    """Compute correlation invariants."""
    if row["expected_overlap"] > 0:
        row["correlation_ratio"] = row["N_joint"] / row["expected_overlap"]
    else:
        row["correlation_ratio"] = 0.0
    # Adversarial gap: expected - actual (positive => bands AVOID targets)
    row["adversarial_gap"] = row["expected_overlap"] - row["N_joint"]
    # kG + kA - (n-1): LRC-shape has this = 0
    row["lrc_shape_balance"] = row["kG"] + row["kA"] - (row["n"] - 1)
    return row


def main():
    print("=" * 78)
    print("PHASE 6c — Correlation analysis: bands vs targets in LRC-shape")
    print("=" * 78)
    rows = load_phase6b_rows()
    rows = [augment(r) for r in rows]
    print(f"Loaded {len(rows)} rows.")

    L_residual = [r for r in rows if r["stratum"] == "L_residual"]
    NL_residual = [r for r in rows if r["stratum"] == "NL_residual"]
    CE_set = [r for r in rows if r["stratum"] == "CE_set"]

    def summary(name, rows, key):
        vals = sorted(r[key] for r in rows)
        if not vals:
            return
        avg = sum(vals) / len(vals)
        print(f"  {name:>13} | min={vals[0]:>10.4f} | median={vals[len(vals)//2]:>10.4f} | "
              f"max={vals[-1]:>10.4f} | mean={avg:>10.4f}")

    print()
    print("INVARIANT: correlation_ratio = N_joint / expected_overlap")
    print("  (≈1 means random independent; <1 means slight negative; 0 means CE)")
    print("-" * 78)
    summary("L_residual", L_residual, "correlation_ratio")
    summary("NL_residual", NL_residual, "correlation_ratio")
    summary("CE_set", CE_set, "correlation_ratio")
    print()

    print("INVARIANT: adversarial_gap = expected_overlap - N_joint")
    print("  (positive: bands AVOID targets; 0: random; negative: bands SEEK targets)")
    print("-" * 78)
    summary("L_residual", L_residual, "adversarial_gap")
    summary("NL_residual", NL_residual, "adversarial_gap")
    summary("CE_set", CE_set, "adversarial_gap")
    print()

    print("INVARIANT: lrc_shape_balance = (kG + kA) - (n - 1)")
    print("  (= 0 for LRC-shape; >0 for OVER-shape; <0 for UNDER-shape)")
    print("-" * 78)
    from collections import Counter
    print(f"  L_residual : {sorted(Counter(r['lrc_shape_balance'] for r in L_residual).items())}")
    print(f"  NL_residual: {sorted(Counter(r['lrc_shape_balance'] for r in NL_residual).items())}")
    print(f"  CE_set     : {sorted(Counter(r['lrc_shape_balance'] for r in CE_set).items())}")
    print()

    # Test: does LRC-shape balance == 0 perfectly separate L_residual from CE?
    L_bal0 = sum(1 for r in L_residual if r["lrc_shape_balance"] == 0)
    CE_bal0 = sum(1 for r in CE_set if r["lrc_shape_balance"] == 0)
    print(f"  L_residual with balance==0: {L_bal0}/{len(L_residual)}")
    print(f"  CE with balance==0:         {CE_bal0}/{len(CE_set)}")
    print()

    # The KEY separator: lrc_class itself
    print("INVARIANT: lrc_class (DI/ModDI vs neither)")
    print("-" * 78)
    from collections import Counter
    print(f"  L_residual : {Counter(r['lrc_class'] for r in L_residual)}")
    print(f"  NL_residual: {Counter(r['lrc_class'] for r in NL_residual)}")
    print(f"  CE_set     : {Counter(r['lrc_class'] for r in CE_set)}")
    print()

    # Now look at CE_set with lrc_shape_balance == 0 but lrc_class == "neither"
    CE_bal0_neither = [r for r in CE_set if r["lrc_shape_balance"] == 0 and r["lrc_class"] == "neither"]
    print(f"CE with kG+kA == n-1 but lrc_class == 'neither': {len(CE_bal0_neither)}")
    if CE_bal0_neither:
        print(f"  These satisfy LRC-shape CARDINALITY but fail other LRC conditions.")
        print(f"  First 10:")
        for r in CE_bal0_neither[:10]:
            print(f"    n={r['n']} G={r['G_speeds']} A={r['A_speeds']} p={r['p']} "
                  f"cIG={r['cIG']} cIA={r['cIA']} n_band={r['n_band_betas']} "
                  f"exp_ovr={r['expected_overlap']:.2f}")
    print()

    # Compound separator: LRC-shape balance == 0 AND expected_overlap > 1
    print("COMPOUND SEPARATOR: lrc_shape_balance == 0 AND expected_overlap > 1")
    print("-" * 78)
    for T in [0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 4.0, 5.0]:
        L_pass = sum(1 for r in L_residual
                     if r["lrc_shape_balance"] == 0 and r["expected_overlap"] > T)
        CE_pass = sum(1 for r in CE_set
                      if r["lrc_shape_balance"] == 0 and r["expected_overlap"] > T)
        L_fail = sum(1 for r in L_residual if not (r["lrc_shape_balance"] == 0 and r["expected_overlap"] > T))
        CE_fail = sum(1 for r in CE_set if not (r["lrc_shape_balance"] == 0 and r["expected_overlap"] > T))
        print(f"  T={T}: L_residual passes {L_pass}/{len(L_residual)}, "
              f"CE passes {CE_pass}/{len(CE_set)}")

    # Even better: lrc_class in {DI, ModDI} (the actual LRC-shape) AND expected_overlap > T
    print()
    print("COMPOUND SEPARATOR: lrc_class in {DI, ModDI} AND expected_overlap > T")
    print("-" * 78)
    for T in [0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 4.0, 5.0]:
        L_pass = sum(1 for r in L_residual
                     if r["lrc_class"] in {"DI", "ModDI"} and r["expected_overlap"] > T)
        CE_pass = sum(1 for r in CE_set
                      if r["lrc_class"] in {"DI", "ModDI"} and r["expected_overlap"] > T)
        print(f"  T={T}: L_residual passes {L_pass}/{len(L_residual)}, "
              f"CE passes {CE_pass}/{len(CE_set)}")

    # The strongest result: LRC-class is the structural marker
    # Within LRC-class, what is the worst-case expected_overlap?
    LRC_class_in_residual = [r for r in rows if r["lrc_class"] in {"DI", "ModDI"}
                             and r["pigeon_deficit"] >= 0]  # pigeonhole fails
    print()
    print(f"LRC-shape pigeonhole-failure cases (all positive by Phase 5): {len(LRC_class_in_residual)}")
    # cross-check: this should equal L_residual count (53)
    assert len(LRC_class_in_residual) == len(L_residual)

    # Within LRC class CE? Should be ZERO.
    LRC_class_CE = [r for r in CE_set if r["lrc_class"] in {"DI", "ModDI"}]
    print(f"LRC-shape COUNTEREXAMPLES (should be ZERO from Phase 3b): {len(LRC_class_CE)}")
    if LRC_class_CE:
        print("  ! UNEXPECTED LRC-shape CE — investigate:")
        for r in LRC_class_CE[:10]:
            print(f"    n={r['n']} G={r['G_speeds']} A={r['A_speeds']} p={r['p']} {r['lrc_class']}")

    # Output the augmented CSV
    if rows:
        fieldnames = list(rows[0].keys())
        os.makedirs(os.path.dirname(CSV_OUT), exist_ok=True)
        with open(CSV_OUT, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=fieldnames)
            w.writeheader()
            for r in rows:
                w.writerow(r)
        print()
        print(f"Wrote {len(rows)} rows to {CSV_OUT}")


if __name__ == "__main__":
    main()
