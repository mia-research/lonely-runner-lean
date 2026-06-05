"""
Phase 7c — Residual pattern enumeration.

Goal: characterize the LRC-shape pigeonhole-failure cases (53 from Phase 5
at n ∈ {4,5,6} + 22 from Phase 7a at n ∈ {7,8}) as a structural pattern
family, and check finiteness.

Patterns to test:
  1. p small (=2 or 3)
  2. kA small (=1 or 2)
  3. L_G small relative to nLA
  4. (n, kG, kA) signature

Output: a table of residual patterns + a candidate finite-list assertion.
"""

import csv
from collections import defaultdict, Counter


CSV_PHASE5 = "/Users/trentpalelei/Desktop/Math Ex/reports/phase6_residual_arithmetic.csv"
CSV_PHASE7A = "/Users/trentpalelei/Desktop/Math Ex/reports/phase7a_extended_search.csv"


def load_phase5_lrc_residual():
    """L_residual stratum from phase6 enrichment (which loaded phase5)."""
    rows = []
    with open(CSV_PHASE5, newline="") as f:
        for r in csv.DictReader(f):
            if r["stratum"] == "L_residual":
                for k in ("n", "p", "kG", "kA", "L_G", "L_A", "nLA", "cIG",
                          "cIA", "n_band_betas", "N_joint"):
                    r[k] = int(r[k])
                rows.append(r)
    return rows


def load_phase7a_lrc_residual():
    """LRC-shape pigeonhole-failure rows from phase 7a."""
    rows = []
    with open(CSV_PHASE7A, newline="") as f:
        for r in csv.DictReader(f):
            for k in ("n", "p", "kG", "kA", "L_G", "L_A", "nLA", "cIG",
                      "cIA", "n_band_betas", "pigeonhole_holds", "N_joint"):
                r[k] = int(r[k])
            if r["pigeonhole_holds"] == 0 and r["lrc_class"] in {"DI", "ModDI"}:
                rows.append(r)
    return rows


def main():
    print("=" * 78)
    print("PHASE 7c — Residual pattern characterization (LRC-shape, pigeonhole fails)")
    print("=" * 78)
    p5 = load_phase5_lrc_residual()
    p7 = load_phase7a_lrc_residual()
    all_residual = p5 + p7
    print(f"Phase 5/6 residual (n ∈ {{4,5,6}}): {len(p5)}")
    print(f"Phase 7a residual (n ∈ {{7,8,9}}): {len(p7)}")
    print(f"TOTAL residual: {len(all_residual)}")
    print()

    print("Distribution by n:")
    n_counts = Counter(r["n"] for r in all_residual)
    for n in sorted(n_counts):
        print(f"  n={n}: {n_counts[n]} residual cases")
    print()

    print("Distribution by p:")
    p_counts = Counter(r["p"] for r in all_residual)
    for p in sorted(p_counts):
        print(f"  p={p}: {p_counts[p]} residual cases")
    print()

    print("Distribution by (kG, kA):")
    k_counts = Counter((r["kG"], r["kA"]) for r in all_residual)
    for k in sorted(k_counts):
        print(f"  (kG={k[0]}, kA={k[1]}): {k_counts[k]} residual cases")
    print()

    print("Distribution by (n, p):")
    np_counts = Counter((r["n"], r["p"]) for r in all_residual)
    for np in sorted(np_counts):
        print(f"  n={np[0]}, p={np[1]}: {np_counts[np]} residual cases")
    print()

    print("Distribution by lrc_class:")
    c_counts = Counter(r["lrc_class"] for r in all_residual)
    for c in sorted(c_counts):
        print(f"  {c}: {c_counts[c]}")
    print()

    print("Range stats:")
    for key in ("L_G", "L_A", "cIG", "cIA", "n_band_betas", "N_joint"):
        vals = sorted(r[key] for r in all_residual)
        print(f"  {key}: min={vals[0]}, median={vals[len(vals)//2]}, max={vals[-1]}")
    print()

    # All-residual table (sorted by n, then p)
    print("ALL RESIDUAL CASES (sorted by n, p):")
    print("-" * 78)
    keys_show = ["n", "G_speeds", "A_speeds", "p", "kG", "kA", "L_G", "L_A",
                 "cIG", "cIA", "n_band_betas", "N_joint", "lrc_class"]
    print(" | ".join(f"{k:>14}" for k in keys_show))
    all_residual.sort(key=lambda r: (r["n"], r["p"]))
    for r in all_residual:
        print(" | ".join(f"{r[k]!s:>14}" for k in keys_show))
    print()

    # Pattern: is the residual confined to small (p, kA)?
    print("PATTERN HYPOTHESIS: small (p, kA) suffices")
    print("-" * 78)
    small_p_kA = sum(1 for r in all_residual if r["p"] <= 3 and r["kA"] <= 2)
    print(f"  Residual with p ≤ 3 AND kA ≤ 2: {small_p_kA} / {len(all_residual)}")
    outside = [r for r in all_residual if not (r["p"] <= 3 and r["kA"] <= 2)]
    print(f"  Outside (need investigation): {len(outside)}")
    if outside:
        for r in outside:
            print(f"    n={r['n']} G={r['G_speeds']} A={r['A_speeds']} p={r['p']} "
                  f"kG={r['kG']} kA={r['kA']} N_joint={r['N_joint']}")
    print()

    # Tightness of pigeonhole failure: deficit = nLA - (n_band_betas + cIA)
    print("PIGEONHOLE DEFICIT (= nLA - (|B| + |I_A|)):")
    print("-" * 78)
    deficits = sorted(r["nLA"] - r["n_band_betas"] - r["cIA"] for r in all_residual)
    print(f"  min={deficits[0]}, median={deficits[len(deficits)//2]}, max={deficits[-1]}")
    print(f"  How many have deficit = 0 (tightest possible)?")
    d0 = sum(1 for r in all_residual if r["nLA"] - r["n_band_betas"] - r["cIA"] == 0)
    print(f"  {d0} / {len(all_residual)}")
    print()


if __name__ == "__main__":
    main()
