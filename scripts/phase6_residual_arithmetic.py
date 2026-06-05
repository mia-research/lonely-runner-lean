"""
Phase 6 — Residual arithmetic-alignment structure of pigeonhole-failure positives.

Background: Phase 5 proved the Pigeonhole Sub-condition
    |B| + |I_A| > n L_A  ==>  conjecture holds (N_joint >= 1).
Empirics: perfect separation of CE vs positives in one direction
    - All 681 CE fail pigeonhole.
    - 34,825 of 37,983 positives satisfy pigeonhole.
    - 3,158 positives FAIL pigeonhole but are still positive
      (arithmetic-alignment cases).
    - Of the 5,517 LRC-shape inputs, 53 fail pigeonhole (0.96%).

Phase 6 goal: investigate the 53 LRC-shape residual cases and search for a
sub-invariant that perfectly separates them from CE.

Stratification (within {pigeonhole fails}):
    L_residual   = LRC-shape (DI / ModDI) inputs that fail pigeonhole       (53)
    NL_residual  = non-LRC-shape positives that fail pigeonhole             (3,158)
    CE_set       = counterexamples (all fail pigeonhole)                    (681)

For each stratum we recompute fine structural invariants by re-evaluating the
input (n, G_speeds, A_speeds, p) and emit a dataset for slicing.

Output:
    reports/phase6_residual_arithmetic.csv
    Console: stratum sizes, invariant histograms, candidate-separator scan,
             and an enumeration of any clean separators.
"""

import csv
import itertools
import math
import os
from collections import Counter, defaultdict
from functools import reduce


CSV_IN = "/Users/trentpalelei/Desktop/Math Ex/reports/phase5_residue_structure.csv"
CSV_OUT = "/Users/trentpalelei/Desktop/Math Ex/reports/phase6_residual_arithmetic.csv"


def gcd_list(xs):
    return reduce(math.gcd, xs, 0)


def lcm(a, b):
    return a * b // math.gcd(a, b)


def lcm_list(xs):
    return reduce(lcm, xs, 1)


def isprime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            return False
        i += 2
    return True


def good_cell_idx(speeds, n, L):
    result = []
    for m in range(n * L):
        ok = True
        for v in speeds:
            d = L // v
            r = (m // d) % n
            if not (1 <= r <= n - 2):
                ok = False
                break
        if ok:
            result.append(m)
    return result


def fine_structure(n, G_speeds, A_speeds, p):
    """Compute extended structural invariants for a single input."""
    L_G = lcm_list(G_speeds)
    L_A = lcm_list(A_speeds)
    nLG = n * L_G
    nLA = n * L_A
    nLGLA = nLG * L_A

    I_G = good_cell_idx(G_speeds, n, L_G)
    I_A = good_cell_idx(A_speeds, n, L_A)

    # Shift residues mod n L_G
    shift_set = set((a * p) % nLG for a in I_G)
    # Shift residues mod L_A (β-start residue class)
    shift_res_mod_LA = set((r * L_A // L_G) % L_A for r in shift_set)  # noqa

    # Build band β-coverage in nLGLA space
    band_betas = set()
    # per-residue-class counts: for each residue r in [0,L_A),
    # how many β in [0, n L_A) with β ≡ r are covered
    per_res_cover = defaultdict(set)
    for a in I_G:
        r = (a * p) % nLG
        band_start = r * L_A
        for e in range(L_A * p):
            pos = (band_start + e) % nLGLA
            beta = pos // L_G
            band_betas.add(beta)
            per_res_cover[beta % L_A].add(beta)

    target_betas = set(I_A)
    target_res = set(b % L_A for b in target_betas)
    intersect = band_betas & target_betas

    # Per-residue saturation: how full is each covered residue class?
    # In each residue class mod L_A, the maximum number of β values is n
    # (since β ∈ [0, n L_A) and there are n values per residue class).
    band_res_seen = set(per_res_cover.keys())
    missed_res = set(range(L_A)) - band_res_seen

    full_classes = sum(1 for r in band_res_seen if len(per_res_cover[r]) == n)
    partial_classes = sum(1 for r in band_res_seen if 1 <= len(per_res_cover[r]) < n)

    # Within-residue gap: in the residue classes containing targets,
    # how many target β's are MISSED by the bands?
    within_res_target_missed = 0
    within_res_target_total = 0
    for b in target_betas:
        r = b % L_A
        within_res_target_total += 1
        if b not in per_res_cover.get(r, set()):
            within_res_target_missed += 1

    # Residue-mode of I_G mod L_G (Phase 5 invariant, retained)
    res_G_mod_LG = len(set(a % L_G for a in I_G))

    # Density bounds (Lemma 4.1 style)
    vmax = max(G_speeds + A_speeds)
    cIG_lower_lem41 = max(1, math.ceil(2 * L_G / ((n - 1) * vmax)))  # comparison
    cIA_lower_lem41 = max(1, math.ceil(2 * L_A / ((n - 1) * vmax)))

    # Pigeonhole slack/deficit
    deficit = (n * L_A) - (len(band_betas) + len(I_A))  # ≥ 0 means pigeonhole FAILS

    # Coverage density
    cover_density = len(band_betas) / (n * L_A)

    return {
        "n": n,
        "G_speeds": "-".join(map(str, G_speeds)),
        "A_speeds": "-".join(map(str, A_speeds)),
        "p": p,
        "kG": len(G_speeds),
        "kA": len(A_speeds),
        "L_G": L_G,
        "L_A": L_A,
        "nLA": nLA,
        "cIG": len(I_G),
        "cIA": len(I_A),
        "res_G_mod_LG": res_G_mod_LG,
        "n_shift_residues_mod_LA": len(shift_res_mod_LA),
        "n_band_betas": len(band_betas),
        "n_band_betas_mod_LA": len(band_res_seen),
        "n_missed_res_mod_LA": len(missed_res),
        "full_res_classes": full_classes,
        "partial_res_classes": partial_classes,
        "within_res_target_total": within_res_target_total,
        "within_res_target_missed": within_res_target_missed,
        "deficit": deficit,
        "cover_density": round(cover_density, 4),
        "N_joint": len(intersect),
        "cIG_lower_lem41": cIG_lower_lem41,
        "cIA_lower_lem41": cIA_lower_lem41,
        "vmax": vmax,
    }


def parse_speeds(s):
    return [int(x) for x in s.split("-")]


def load_phase5_rows():
    rows = []
    with open(CSV_IN, newline="") as f:
        for r in csv.DictReader(f):
            r["n"] = int(r["n"])
            r["p"] = int(r["p"])
            r["kG"] = int(r["kG"])
            r["kA"] = int(r["kA"])
            r["L_G"] = int(r["L_G"])
            r["L_A"] = int(r["L_A"])
            r["cIG"] = int(r["cIG"])
            r["cIA"] = int(r["cIA"])
            r["n_band_betas"] = int(r["n_band_betas"])
            r["N_joint"] = int(r["N_joint"])
            rows.append(r)
    return rows


def stratify(rows):
    """Partition rows into the 3 strata of interest (pigeonhole-failure focus)."""
    L_residual, NL_residual, CE_set = [], [], []
    pigeon_holds, all_lrc, all_ce = 0, 0, 0
    for r in rows:
        pigeon_ok = (r["n_band_betas"] + r["cIA"]) > (r["n"] * r["L_A"])
        is_lrc = r["lrc_class"] in {"DI", "ModDI"}
        if is_lrc:
            all_lrc += 1
        if r["N_joint"] == 0:
            all_ce += 1
        if pigeon_ok:
            pigeon_holds += 1
            continue
        # pigeon_ok is False
        if r["N_joint"] == 0:
            CE_set.append(r)
        elif is_lrc:
            L_residual.append(r)
        else:
            NL_residual.append(r)
    return L_residual, NL_residual, CE_set, {
        "total": len(rows),
        "pigeon_holds": pigeon_holds,
        "all_lrc": all_lrc,
        "all_ce": all_ce,
    }


def enrich(rows):
    """Recompute fine_structure for each row."""
    out = []
    for r in rows:
        G_speeds = parse_speeds(r["G_speeds"])
        A_speeds = parse_speeds(r["A_speeds"])
        fs = fine_structure(r["n"], G_speeds, A_speeds, r["p"])
        fs["lrc_class"] = r["lrc_class"]
        out.append(fs)
    return out


def histogram(rows, key):
    return Counter(r[key] for r in rows)


def print_hist(name, rows, key):
    h = histogram(rows, key)
    items = sorted(h.items())
    if not items:
        print(f"  {name}: (empty)")
        return
    summary = ", ".join(f"{k}:{v}" for k, v in items[:20])
    extra = "" if len(items) <= 20 else f"  (+{len(items)-20} more values)"
    print(f"  {name}: {summary}{extra}")


def candidate_separators(L_residual, CE_set):
    """
    Search for a single-invariant (or simple compound) condition C such that:
      - C(x) holds for every x in L_residual
      - C(x) fails for every x in CE_set
    Equivalent: a property that all 53 residual-LRC have but no CE has.
    """
    print()
    print("SEPARATOR SEARCH — properties that hold for ALL L_residual and NO CE")
    print("-" * 78)

    # Build per-key value sets
    keys = [
        "p", "kG", "kA", "n_missed_res_mod_LA", "full_res_classes",
        "within_res_target_missed", "n_shift_residues_mod_LA",
        "res_G_mod_LG", "cIG", "cIA",
    ]
    for k in keys:
        L_vals = set(r[k] for r in L_residual)
        CE_vals = set(r[k] for r in CE_set)
        # Property "x[k] in L_vals"
        # We want CE_vals ∩ L_vals == ∅ for this to be a perfect separator.
        if L_vals and not (L_vals & CE_vals):
            print(f"  PERFECT (single-key): {k} in {sorted(L_vals)} (CE: {sorted(CE_vals)[:8]}...)")
        else:
            # check threshold separators
            L_min, L_max = min(L_vals), max(L_vals)
            CE_min, CE_max = min(CE_vals), max(CE_vals)
            if L_min > CE_max:
                print(f"  PERFECT (threshold): {k} >= {L_min}  (CE has {k} <= {CE_max})")
            elif L_max < CE_min:
                print(f"  PERFECT (threshold): {k} <= {L_max}  (CE has {k} >= {CE_min})")

    # Compound: missed_res = 0 (full residue coverage)
    L_missed0 = sum(1 for r in L_residual if r["n_missed_res_mod_LA"] == 0)
    CE_missed0 = sum(1 for r in CE_set if r["n_missed_res_mod_LA"] == 0)
    print()
    print(f"  COMPOUND: n_missed_res_mod_LA == 0")
    print(f"    L_residual: {L_missed0}/{len(L_residual)}  CE: {CE_missed0}/{len(CE_set)}")

    # Compound: within_res_target_missed = 0
    L_wrt0 = sum(1 for r in L_residual if r["within_res_target_missed"] == 0)
    CE_wrt0 = sum(1 for r in CE_set if r["within_res_target_missed"] == 0)
    print(f"  COMPOUND: within_res_target_missed == 0 (defn of positivity)")
    print(f"    L_residual: {L_wrt0}/{len(L_residual)}  CE: {CE_wrt0}/{len(CE_set)}")

    # Compound: full residue coverage AND small partial classes
    L_fullc = sum(1 for r in L_residual if r["partial_res_classes"] == 0)
    CE_fullc = sum(1 for r in CE_set if r["partial_res_classes"] == 0)
    print(f"  COMPOUND: partial_res_classes == 0 (all covered classes are FULL)")
    print(f"    L_residual: {L_fullc}/{len(L_residual)}  CE: {CE_fullc}/{len(CE_set)}")

    # New invariant candidate: shift residue coverage
    L_full_shift = sum(1 for r in L_residual if r["n_shift_residues_mod_LA"] == r["L_A"])
    CE_full_shift = sum(1 for r in CE_set if r["n_shift_residues_mod_LA"] == r["L_A"])
    print(f"  COMPOUND: n_shift_residues_mod_LA == L_A (band starts hit ALL L_A residues)")
    print(f"    L_residual: {L_full_shift}/{len(L_residual)}  CE: {CE_full_shift}/{len(CE_set)}")

    # SUM: n_band_betas_mod_LA + len(target_residues) > L_A (β-residue pigeonhole)
    # This is a strict-residue pigeonhole. We need target residues — use cIA
    # as a proxy upper bound on the number of distinct residues.
    # Actual residue pigeonhole: n_band_betas_mod_LA + |target_residues_mod_LA| > L_A
    # Cheaper proxy: n_band_betas_mod_LA == L_A (full residue coverage by bands)
    # already shown above.


def main():
    print("=" * 78)
    print("PHASE 6 — Residual arithmetic-alignment structure")
    print("=" * 78)

    rows = load_phase5_rows()
    print(f"Loaded {len(rows)} Phase 5 rows.")

    L_residual_raw, NL_residual_raw, CE_set_raw, summary = stratify(rows)
    print(f"Total scanned: {summary['total']}")
    print(f"All LRC-shape: {summary['all_lrc']}")
    print(f"All CE: {summary['all_ce']}")
    print(f"Pigeonhole holds: {summary['pigeon_holds']}")
    print()
    print(f"Pigeonhole-failure strata:")
    print(f"  L_residual  (LRC-shape positive, pigeonhole fails): {len(L_residual_raw)}")
    print(f"  NL_residual (non-LRC positive, pigeonhole fails):   {len(NL_residual_raw)}")
    print(f"  CE_set      (CE, all fail pigeonhole):              {len(CE_set_raw)}")
    print()

    # Sanity-check: stratified counts must match expectations
    assert summary["all_ce"] == len(CE_set_raw), \
        f"All CE should fail pigeonhole, got {summary['all_ce']} != {len(CE_set_raw)}"

    print("Enriching strata with fine structural invariants ...")
    L_residual = enrich(L_residual_raw)
    NL_residual = enrich(NL_residual_raw)
    CE_set = enrich(CE_set_raw)
    print("  Done.")
    print()

    print("INVARIANT HISTOGRAMS — L_residual (53 expected)")
    print("-" * 78)
    for k in ["p", "kG", "kA", "n_missed_res_mod_LA", "full_res_classes",
              "partial_res_classes", "within_res_target_missed",
              "n_shift_residues_mod_LA", "res_G_mod_LG", "cIG", "cIA"]:
        print_hist(k, L_residual, k)
    print()

    print("INVARIANT HISTOGRAMS — CE_set (681 expected)")
    print("-" * 78)
    for k in ["p", "kG", "kA", "n_missed_res_mod_LA", "full_res_classes",
              "partial_res_classes", "within_res_target_missed",
              "n_shift_residues_mod_LA", "res_G_mod_LG", "cIG", "cIA"]:
        print_hist(k, CE_set, k)
    print()

    print("INVARIANT HISTOGRAMS — NL_residual (3,158 expected)")
    print("-" * 78)
    for k in ["p", "kG", "kA", "n_missed_res_mod_LA", "full_res_classes",
              "partial_res_classes", "within_res_target_missed",
              "n_shift_residues_mod_LA", "res_G_mod_LG", "cIG", "cIA"]:
        print_hist(k, NL_residual, k)
    print()

    candidate_separators(L_residual, CE_set)
    print()

    # Show all 53 L_residual rows for manual inspection
    print("L_residual — all 53 cases:")
    print("-" * 78)
    keys_show = ["n", "G_speeds", "A_speeds", "p", "kG", "kA", "L_G", "L_A",
                 "cIG", "cIA", "n_band_betas", "n_missed_res_mod_LA",
                 "within_res_target_missed", "N_joint", "lrc_class"]
    print(" | ".join(f"{k:>20}" for k in keys_show))
    for r in L_residual:
        print(" | ".join(f"{r[k]!s:>20}" for k in keys_show))
    print()

    # CSV out — all enriched rows
    fieldnames = list(L_residual[0].keys()) if L_residual else []
    all_rows = [{**r, "stratum": "L_residual"} for r in L_residual] + \
               [{**r, "stratum": "NL_residual"} for r in NL_residual] + \
               [{**r, "stratum": "CE_set"} for r in CE_set]
    if all_rows:
        fieldnames = list(all_rows[0].keys())
    os.makedirs(os.path.dirname(CSV_OUT), exist_ok=True)
    with open(CSV_OUT, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        for r in all_rows:
            w.writerow(r)
    print(f"Wrote {len(all_rows)} rows to {CSV_OUT}")


if __name__ == "__main__":
    main()
