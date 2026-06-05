"""
Phase 6b — Refined separator search using density-product invariants.

Phase 6 showed:
  - 52/53 L_residual have FULL residue coverage mod L_A (n_missed_res_mod_LA == 0).
  - All 53 L_residual have NO full residue class (full_res_classes == 0).
  - 420/681 CE also have full residue coverage; 632/681 CE have no full classes.

So full-residue-coverage is NOT a perfect separator. We need a quantitative
density-product separator.

Candidate invariants (Phase 6b):
  1. expected_overlap = n_band_betas * cIA / (n * L_A)
     (mean intersection size under random distribution)
  2. cIG * cIA / (n * L_A) — speed-cell density product
  3. expected_overlap_per_residue = (n_band_betas / L_A) * cIA / (n * L_A) ...
  4. min_residue_coverage = min over target residues of |bands ∩ that residue class|
  5. cIG * (L_A * p / L_G) (effective band length per cell × cIG, scaled)
  6. n_shift_residues_mod_LA — distinct shift classes touched

We compare distributions and search for a clean separator between L_residual and
CE_set, restricted to pigeonhole-failure stratum.
"""

import csv
import itertools
import math
import os
from collections import Counter, defaultdict
from functools import reduce


CSV_IN = "/Users/trentpalelei/Desktop/Math Ex/reports/phase6_residual_arithmetic.csv"
CSV_OUT = "/Users/trentpalelei/Desktop/Math Ex/reports/phase6b_density_separator.csv"


def load_phase6_rows():
    rows = []
    with open(CSV_IN, newline="") as f:
        for r in csv.DictReader(f):
            for k in ("n", "p", "kG", "kA", "L_G", "L_A", "nLA", "cIG", "cIA",
                      "res_G_mod_LG", "n_shift_residues_mod_LA",
                      "n_band_betas", "n_band_betas_mod_LA", "n_missed_res_mod_LA",
                      "full_res_classes", "partial_res_classes",
                      "within_res_target_total", "within_res_target_missed",
                      "deficit", "N_joint", "vmax"):
                if k in r:
                    r[k] = int(r[k])
            r["cover_density"] = float(r["cover_density"])
            rows.append(r)
    return rows


def augment(row):
    """Compute density-product invariants."""
    nLA = row["n"] * row["L_A"]
    # Expected overlap (band β-coverage with targets, random model)
    row["expected_overlap"] = row["n_band_betas"] * row["cIA"] / nLA
    # Density product of cell sets (before band expansion)
    row["cell_density_product"] = row["cIG"] * row["cIA"] / nLA
    # Effective band length per cell: bands have length L_A * p, normalized
    row["band_len_per_cell"] = (row["L_A"] * row["p"]) / row["L_G"]
    # cIG * band_len_per_cell — total β-coverage if bands disjoint
    row["raw_band_coverage"] = row["cIG"] * row["L_A"] * row["p"] / row["L_G"]
    # Overlap ratio: how much do bands overlap with each other?
    row["band_overlap_ratio"] = row["raw_band_coverage"] / max(row["n_band_betas"], 1)
    # Pigeonhole sufficiency margin
    row["pigeon_deficit"] = nLA - (row["n_band_betas"] + row["cIA"])
    # Target density
    row["target_density"] = row["cIA"] / nLA
    # Coverage density (recomputed)
    row["coverage_density"] = row["n_band_betas"] / nLA
    return row


def main():
    print("=" * 78)
    print("PHASE 6b — Density-product separator search")
    print("=" * 78)
    rows = load_phase6_rows()
    print(f"Loaded {len(rows)} Phase 6 enriched rows.")

    # Augment every row
    rows = [augment(r) for r in rows]

    L_residual = [r for r in rows if r["stratum"] == "L_residual"]
    NL_residual = [r for r in rows if r["stratum"] == "NL_residual"]
    CE_set = [r for r in rows if r["stratum"] == "CE_set"]
    print(f"  L_residual: {len(L_residual)}")
    print(f"  NL_residual: {len(NL_residual)}")
    print(f"  CE_set: {len(CE_set)}")
    print()

    def summary(name, rows, key):
        vals = sorted(r[key] for r in rows)
        if not vals:
            return
        avg = sum(vals) / len(vals)
        print(f"  {name:>13} | min={vals[0]:>10.4f} | median={vals[len(vals)//2]:>10.4f} | "
              f"max={vals[-1]:>10.4f} | mean={avg:>10.4f}")

    print("INVARIANT: expected_overlap = n_band_betas * cIA / (n L_A)")
    print("-" * 78)
    summary("L_residual", L_residual, "expected_overlap")
    summary("NL_residual", NL_residual, "expected_overlap")
    summary("CE_set", CE_set, "expected_overlap")
    print()

    print("INVARIANT: cell_density_product = cIG * cIA / (n L_A)")
    print("-" * 78)
    summary("L_residual", L_residual, "cell_density_product")
    summary("NL_residual", NL_residual, "cell_density_product")
    summary("CE_set", CE_set, "cell_density_product")
    print()

    print("INVARIANT: raw_band_coverage = cIG * L_A * p / L_G")
    print("-" * 78)
    summary("L_residual", L_residual, "raw_band_coverage")
    summary("NL_residual", NL_residual, "raw_band_coverage")
    summary("CE_set", CE_set, "raw_band_coverage")
    print()

    print("INVARIANT: band_overlap_ratio = raw_band_coverage / n_band_betas")
    print("-" * 78)
    summary("L_residual", L_residual, "band_overlap_ratio")
    summary("NL_residual", NL_residual, "band_overlap_ratio")
    summary("CE_set", CE_set, "band_overlap_ratio")
    print()

    print("INVARIANT: pigeon_deficit = nLA - (n_band_betas + cIA)")
    print("-" * 78)
    summary("L_residual", L_residual, "pigeon_deficit")
    summary("NL_residual", NL_residual, "pigeon_deficit")
    summary("CE_set", CE_set, "pigeon_deficit")
    print()

    print("INVARIANT: target_density = cIA / (n L_A)")
    print("-" * 78)
    summary("L_residual", L_residual, "target_density")
    summary("NL_residual", NL_residual, "target_density")
    summary("CE_set", CE_set, "target_density")
    print()

    print("INVARIANT: coverage_density = n_band_betas / (n L_A)")
    print("-" * 78)
    summary("L_residual", L_residual, "coverage_density")
    summary("NL_residual", NL_residual, "coverage_density")
    summary("CE_set", CE_set, "coverage_density")
    print()

    # SEPARATOR SEARCH: is there a threshold T for expected_overlap that
    # perfectly separates L_residual (all > T) from CE (all <= T)?
    print("THRESHOLD SEPARATOR SEARCH")
    print("-" * 78)

    def threshold_test(rows_pos, rows_neg, key, dir_):
        """Test if there's a threshold T with rows_pos[key] (dir_) T for all pos
        and not for any neg."""
        pos_vals = [r[key] for r in rows_pos]
        neg_vals = [r[key] for r in rows_neg]
        if dir_ == ">":
            T = max(neg_vals) if neg_vals else -math.inf
            if min(pos_vals) > T:
                return ("PERFECT", T)
            else:
                # Count overlap
                violators_pos = sum(1 for v in pos_vals if v <= T)
                return ("PARTIAL", T, violators_pos)
        else:  # "<"
            T = min(neg_vals) if neg_vals else math.inf
            if max(pos_vals) < T:
                return ("PERFECT", T)
            else:
                violators_pos = sum(1 for v in pos_vals if v >= T)
                return ("PARTIAL", T, violators_pos)

    for key in ["expected_overlap", "cell_density_product", "raw_band_coverage",
                "band_overlap_ratio", "coverage_density", "target_density",
                "cIG", "cIA", "n_band_betas", "n_band_betas_mod_LA",
                "L_G", "L_A"]:
        # L_residual > CE
        L_min = min(r[key] for r in L_residual)
        CE_max = max(r[key] for r in CE_set)
        L_max = max(r[key] for r in L_residual)
        CE_min = min(r[key] for r in CE_set)
        if L_min > CE_max:
            print(f"  PERFECT: L_residual[{key}] > {CE_max} (separated by gap)")
        elif L_max < CE_min:
            print(f"  PERFECT: L_residual[{key}] < {CE_min} (separated by gap)")
        else:
            # Compute "best" threshold and its error rate
            best_err = float("inf")
            best_T = None
            best_dir = None
            all_vals = sorted(set([r[key] for r in L_residual] +
                                  [r[key] for r in CE_set]))
            for T in all_vals:
                # Test L_residual > T separates positively
                # L should have > T (be "good"), CE should have <= T
                err = sum(1 for r in L_residual if r[key] <= T) + \
                      sum(1 for r in CE_set if r[key] > T)
                if err < best_err:
                    best_err = err
                    best_T = T
                    best_dir = ">"
                # Test other direction
                err = sum(1 for r in L_residual if r[key] >= T) + \
                      sum(1 for r in CE_set if r[key] < T)
                if err < best_err:
                    best_err = err
                    best_T = T
                    best_dir = "<"
            print(f"  {key}: best threshold {key} {best_dir} {best_T} "
                  f"misclassifies {best_err} / {len(L_residual)+len(CE_set)}")

    # Try compound separator: expected_overlap > 0 AND another condition?
    print()
    print("COMPOUND SEPARATOR: expected_overlap >= K threshold")
    print("-" * 78)
    for K in [0.5, 1.0, 1.5, 2.0, 3.0, 5.0, 10.0]:
        L_below = sum(1 for r in L_residual if r["expected_overlap"] < K)
        CE_below = sum(1 for r in CE_set if r["expected_overlap"] < K)
        L_above = sum(1 for r in L_residual if r["expected_overlap"] >= K)
        CE_above = sum(1 for r in CE_set if r["expected_overlap"] >= K)
        print(f"  K={K}: L_residual[<{K}]={L_below}  CE[<{K}]={CE_below}  "
              f"L_residual[>={K}]={L_above}  CE[>={K}]={CE_above}")

    print()
    print("COMPOUND SEPARATOR: cell_density_product >= K threshold")
    print("-" * 78)
    for K in [0.5, 1.0, 1.5, 2.0, 3.0, 5.0]:
        L_below = sum(1 for r in L_residual if r["cell_density_product"] < K)
        CE_below = sum(1 for r in CE_set if r["cell_density_product"] < K)
        L_above = sum(1 for r in L_residual if r["cell_density_product"] >= K)
        CE_above = sum(1 for r in CE_set if r["cell_density_product"] >= K)
        print(f"  K={K}: L_residual[<{K}]={L_below}  CE[<{K}]={CE_below}  "
              f"L_residual[>={K}]={L_above}  CE[>={K}]={CE_above}")

    print()
    print("RANKED L_residual by expected_overlap (smallest first):")
    print("-" * 78)
    L_residual.sort(key=lambda r: r["expected_overlap"])
    print(f"{'n':>3} {'G':>15} {'A':>10} {'p':>3} {'cIG':>5} {'cIA':>5} "
          f"{'n_band':>7} {'nLA':>5} {'exp_ovr':>9} {'cell_dp':>8} {'N_joint':>7}")
    for r in L_residual[:15]:
        print(f"{r['n']:>3} {r['G_speeds']:>15} {r['A_speeds']:>10} {r['p']:>3} "
              f"{r['cIG']:>5} {r['cIA']:>5} {r['n_band_betas']:>7} {r['nLA']:>5} "
              f"{r['expected_overlap']:>9.3f} {r['cell_density_product']:>8.3f} "
              f"{r['N_joint']:>7}")
    print()

    print("RANKED CE_set by expected_overlap (largest first):")
    print("-" * 78)
    CE_set.sort(key=lambda r: r["expected_overlap"], reverse=True)
    print(f"{'n':>3} {'G':>15} {'A':>10} {'p':>3} {'cIG':>5} {'cIA':>5} "
          f"{'n_band':>7} {'nLA':>5} {'exp_ovr':>9} {'cell_dp':>8} {'N_joint':>7}")
    for r in CE_set[:15]:
        print(f"{r['n']:>3} {r['G_speeds']:>15} {r['A_speeds']:>10} {r['p']:>3} "
              f"{r['cIG']:>5} {r['cIA']:>5} {r['n_band_betas']:>7} {r['nLA']:>5} "
              f"{r['expected_overlap']:>9.3f} {r['cell_density_product']:>8.3f} "
              f"{r['N_joint']:>7}")

    # Output CSV
    if rows:
        fieldnames = list(rows[0].keys())
        os.makedirs(os.path.dirname(CSV_OUT), exist_ok=True)
        with open(CSV_OUT, "w", newline="") as f:
            w = csv.DictWriter(f, fieldnames=fieldnames)
            w.writeheader()
            for r in rows:
                w.writerow(r)
        print()
        print(f"Wrote {len(rows)} augmented rows to {CSV_OUT}")


if __name__ == "__main__":
    main()
