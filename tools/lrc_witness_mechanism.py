"""
lrc_witness_mechanism.py
========================
Investigates the "missing complement" mechanism behind Case R> witnesses.

For each config, at the witness t* = (11j*+1)/(11*p_b):
  - Identifies the ANCHOR runner p_b (the one at ||p_b * t*|| = 1/11 exactly)
  - Computes the BAD ZONE: all integers c in [1, p_10] with ||c * t*|| < 1/11
  - Splits into PRESENT-bad (sanity: should be empty) and ABSENT-bad (the "missing complements")
  - Tests the Missing Complement Hypothesis: absent_bad_count >= 1 for ALL configs

Key question: what is the distribution of absent_bad_count across all configs?
  Scenario A: always = 1  → unified closed-form proof possible
  Scenario B: always >= 1 → unified existence proof possible
  Scenario C: sometimes = 0 → some configs self-contained, need separate argument
"""

import sys
import random
from fractions import Fraction
from collections import Counter

# ── import harness ─────────────────────────────────────────────────────────────
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from lrc_case_r_harness import (
    check_config,
    dist_to_nearest_int,
    generate_type_a,
    generate_type_b,
    generate_type_c,
)


# ── core mechanism functions ───────────────────────────────────────────────────

def find_anchor_runner(speeds, witness_t, n=11):
    """
    Find the anchor runner p_b and index j* such that witness_t = (11j*+1)/(11*p_b).

    The anchor is the runner p with ||p * t*|| == 1/n exactly (just entering isolation).
    Among all such runners, return the one with the largest p_b (most constrained).

    Returns (p_b, j_star, N) where N = n * p_b, or None if no exact entry-time match.
    """
    threshold = Fraction(1, n)
    anchors = []
    for p in speeds:
        d = dist_to_nearest_int(Fraction(p) * witness_t)
        if d == threshold:
            # Verify: witness_t = (n*j+1)/(n*p) for some integer j >= 0
            # => n*p*witness_t = n*j + 1 => n*p*witness_t - 1 must be divisible by n
            val = Fraction(n * p) * witness_t  # should be n*j + 1
            remainder = val - int(val)
            if remainder == Fraction(0):
                j_star = int(val) - 1
                if j_star >= 0 and (n * j_star + 1) == int(val) * 0 + int(val):
                    # double-check
                    reconstructed = Fraction(n * j_star + 1, n * p)
                    if reconstructed == witness_t:
                        anchors.append((p, j_star, n * p))
    if not anchors:
        # Fallback: find runner closest to threshold (numerical tolerance)
        # This handles floating-point cases (shouldn't happen with exact fractions)
        return None
    # Return the anchor with highest p_b (tightest constraint)
    anchors.sort(key=lambda x: x[0], reverse=True)
    return anchors[0]


def bad_zone_integers(witness_t, p_b, max_c, n=11):
    """
    For anchor runner p_b at witness_t = (11j*+1)/(11*p_b), find all integers c in [1, max_c]
    with ||c * witness_t|| < 1/n (would block isolation if present as a speed).

    Returns list of bad integers.
    """
    threshold = Fraction(1, n)
    bad = []
    for c in range(1, max_c + 1):
        d = dist_to_nearest_int(Fraction(c) * witness_t)
        if d < threshold:
            bad.append(c)
    return bad


def classify_mechanism(speeds, n=11, verbose=False):
    """
    Full mechanism analysis for one config.

    Returns dict with:
      witness_t        : the witness time (Fraction or None)
      anchor           : (p_b, j_star, N) or None
      present_bad      : list of present speeds in bad zone (should be empty)
      absent_bad       : list of absent integers in [1, p_10] in bad zone
      absent_bad_count : len(absent_bad)
      present_bad_count: len(present_bad)
      frame_size       : N = 11 * p_b
      j_star           : the index
      p_b              : anchor runner speed
      scenario         : 'A'(=1), 'B'(>1), 'C'(=0), 'FAIL'(no witness/anchor)
    """
    result = {
        "witness_t": None,
        "anchor": None,
        "present_bad": [],
        "absent_bad": [],
        "absent_bad_count": -1,
        "present_bad_count": -1,
        "frame_size": None,
        "j_star": None,
        "p_b": None,
        "scenario": "FAIL",
    }

    # Step 1: get witness
    witness_t, _, _, _, _, _ = check_config(speeds, n)
    if witness_t is None:
        result["scenario"] = "FAIL"
        return result
    result["witness_t"] = witness_t

    # Step 2: find anchor runner
    anchor = find_anchor_runner(speeds, witness_t, n)
    if anchor is None:
        result["scenario"] = "FAIL"
        return result
    p_b, j_star, N = anchor
    result["anchor"] = anchor
    result["p_b"] = p_b
    result["j_star"] = j_star
    result["frame_size"] = N

    # Step 3: find all bad integers in [1, p_10]
    p_10 = speeds[-1]
    all_bad = bad_zone_integers(witness_t, p_b, p_10, n)

    speed_set = set(speeds)
    present_bad = [c for c in all_bad if c in speed_set]
    absent_bad = [c for c in all_bad if c not in speed_set]

    result["present_bad"] = present_bad
    result["absent_bad"] = absent_bad
    result["present_bad_count"] = len(present_bad)
    result["absent_bad_count"] = len(absent_bad)

    if len(present_bad) > 0:
        result["scenario"] = "SANITY_FAIL"  # witness is invalid!
    elif len(absent_bad) == 0:
        result["scenario"] = "C"
    elif len(absent_bad) == 1:
        result["scenario"] = "A"
    else:
        result["scenario"] = "B"

    if verbose:
        print(f"  Speeds: {tuple(speeds)}")
        print(f"  Witness t* = {witness_t}  ({float(witness_t):.6f})")
        print(f"  Anchor: p_b={p_b}, j*={j_star}, frame N={N}")
        print(f"  Bad zone integers in [1,{p_10}]: {all_bad}")
        print(f"  Present-bad: {present_bad}  (should be empty)")
        print(f"  Absent-bad: {absent_bad}")
        print(f"  Scenario: {result['scenario']}")

    return result


# ── formula investigation ──────────────────────────────────────────────────────

def investigate_formula(speeds, result, n=11):
    """
    For Scenario A (absent_bad_count == 1): investigate whether j* can be
    expressed as a formula in terms of m (the absent bad integer) and p_b.

    In the pacemaker case: j* = 10 * m^{-1} mod 11.

    General case: m*(11j*+1) ≡ r (mod 11*p_b), where r < p_b (lower bad) or r > 10*p_b.
    The condition is: m*(11j*+1) mod (11*p_b) ∈ [0, p_b) ∪ (10*p_b, 11*p_b).

    Returns dict with formula analysis.
    """
    if result["scenario"] != "A":
        return None

    m = result["absent_bad"][0]
    p_b = result["p_b"]
    j_star = result["j_star"]
    N = result["frame_size"]  # = 11 * p_b

    # Compute the residue
    val = (m * (n * j_star + 1)) % N
    bad_type = "lower" if val < p_b else "upper"

    # For lower bad: val < p_b, so val ≡ m (mod 11), 0 <= val < p_b
    #   m ≡ val (mod 11), val = m mod 11 (if m < 11) or m mod 11 in general
    # For upper bad: val > 10*p_b, val = N - something
    #   val = N - (N - val), and N - val ≡ -m ≡ 11-m (mod 11)

    # Try: does m * (11j*+1) ≡ m (mod 11)?  YES always (universal property)
    mod11_check = (m * (n * j_star + 1)) % n
    assert mod11_check == m % n, f"Universal property violated! m={m}, j*={j_star}"

    # For pacemaker (p_b = 11*p1): j* = 10*m^{-1} mod 11
    p1 = speeds[0]
    is_pacemaker = (p_b == n * p1)
    pacemaker_formula_j = None
    if is_pacemaker and m % n != 0:
        m_inv = pow(int(m % n), -1, n)  # m^{-1} mod 11
        pacemaker_formula_j = (10 * m_inv) % n

    # General formula attempt: j* is the unique j in [1, n-1] with
    # m*(11j+1) mod (11*p_b) < p_b  OR  > 10*p_b
    # => m*j ≡ ? (mod p_b)  combined with the universal mod-11 structure
    #
    # Lower bad: m*(11j+1) = 11*p_b*q + r, r < p_b, r ≡ m (mod 11)
    #   => m*11j ≡ r - m (mod 11*p_b)
    #   => r - m ≡ 0 (mod 11) [since m*11j divisible by 11 and r≡m mod 11] ✓
    #   => m*j ≡ (r - m)/11 (mod p_b)
    #   => j ≡ m^{-1} * (r-m)/11 (mod p_b)  [if gcd(m, p_b) = 1]
    #
    # Upper bad: m*(11j+1) = 11*p_b*q + r, r > 10*p_b
    #   Similar analysis with r = N - s, s < p_b

    # Check if j* satisfies j* ≡ (some formula) mod p_b
    gcd_m_pb = 1
    try:
        m_inv_pb = pow(int(m % p_b), -1, p_b) if m % p_b != 0 else None
    except Exception:
        m_inv_pb = None

    # What formula_j would be if we apply pacemaker-style but mod p_b?
    formula_j_mod_pb = None
    if m_inv_pb is not None:
        formula_j_mod_pb = (10 * m_inv_pb) % p_b

    return {
        "m": m,
        "p_b": p_b,
        "j_star": j_star,
        "N": N,
        "residue": val,
        "bad_type": bad_type,
        "is_pacemaker": is_pacemaker,
        "pacemaker_formula_j": pacemaker_formula_j,
        "pacemaker_matches": (pacemaker_formula_j == j_star) if is_pacemaker else None,
        "m_mod_11": m % n,
        "j_star_mod_11": j_star % n,
        "formula_j_mod_pb": formula_j_mod_pb,
        "j_star_mod_pb": j_star % p_b,
        "formula_matches_mod_pb": (formula_j_mod_pb == j_star % p_b) if formula_j_mod_pb is not None else None,
    }


# ── batch analysis ─────────────────────────────────────────────────────────────

def batch_mechanism_analysis(configs_with_labels, label="", n=11, verbose_first=3):
    """
    Run mechanism analysis on all configs. Print aggregate statistics.

    configs_with_labels: list of (speeds, label_str) or list of speeds
    Returns list of result dicts.
    """
    print(f"\n{'─'*70}")
    print(f"MECHANISM ANALYSIS: {label}")
    print(f"{'─'*70}")

    results = []
    scenario_counts = Counter()
    anchor_is_p10 = 0
    anchor_is_interior = 0
    absent_bad_distribution = Counter()
    formula_matches_pacemaker = 0
    formula_matches_mod_pb = 0
    formula_checked = 0
    scenario_a_formulas = []

    # Normalize input
    if configs_with_labels and isinstance(configs_with_labels[0], (list, tuple)):
        if isinstance(configs_with_labels[0][0], (list,)):
            # list of (speeds, label) pairs
            items = configs_with_labels
        elif isinstance(configs_with_labels[0][0], int):
            # list of speeds (no labels)
            items = [(s, "") for s in configs_with_labels]
        else:
            items = [(s, "") for s in configs_with_labels]
    else:
        items = [(s, "") for s in configs_with_labels]

    n_verbose = 0
    for idx, item in enumerate(items):
        if isinstance(item, tuple) and len(item) == 2 and isinstance(item[1], str):
            speeds, cfg_label = item
        else:
            speeds, cfg_label = item, ""

        be_verbose = (n_verbose < verbose_first)
        if be_verbose:
            print(f"\n  Config #{idx+1}: {cfg_label}")

        res = classify_mechanism(speeds, n=n, verbose=be_verbose)
        if be_verbose:
            n_verbose += 1

        results.append(res)
        scenario_counts[res["scenario"]] += 1
        if res["absent_bad_count"] >= 0:
            absent_bad_distribution[res["absent_bad_count"]] += 1

        # Anchor type
        if res["p_b"] is not None:
            if res["p_b"] == speeds[-1]:
                anchor_is_p10 += 1
            else:
                anchor_is_interior += 1

        # Formula investigation for Scenario A
        if res["scenario"] == "A":
            finfo = investigate_formula(speeds, res, n)
            if finfo is not None:
                formula_checked += 1
                scenario_a_formulas.append(finfo)
                if finfo["is_pacemaker"] and finfo["pacemaker_matches"]:
                    formula_matches_pacemaker += 1
                if finfo["formula_matches_mod_pb"]:
                    formula_matches_mod_pb += 1

    total = len(results)
    print(f"\n  Total configs: {total}")
    print(f"\n  Scenario distribution:")
    for sc, cnt in sorted(scenario_counts.items()):
        pct = 100.0 * cnt / total if total else 0
        desc = {"A": "absent_bad=1 (Unified formula?)",
                "B": "absent_bad>1 (Multiple complements)",
                "C": "absent_bad=0 (Self-contained)",
                "FAIL": "No witness/anchor found",
                "SANITY_FAIL": "Present speed in bad zone (witness invalid!)"}.get(sc, sc)
        print(f"    {sc}: {cnt}/{total} ({pct:.1f}%)  — {desc}")

    print(f"\n  absent_bad_count distribution:")
    for cnt_val in sorted(absent_bad_distribution.keys()):
        freq = absent_bad_distribution[cnt_val]
        pct = 100.0 * freq / total if total else 0
        print(f"    absent_bad={cnt_val}: {freq} configs ({pct:.1f}%)")

    print(f"\n  Anchor runner type:")
    print(f"    Anchor = p_10 (fastest runner): {anchor_is_p10}/{total} ({100.0*anchor_is_p10/total:.1f}%)")
    print(f"    Anchor = interior runner:        {anchor_is_interior}/{total} ({100.0*anchor_is_interior/total:.1f}%)")

    if formula_checked > 0:
        print(f"\n  Formula analysis (Scenario A, {formula_checked} configs):")
        # Pacemaker
        pacemakers = [f for f in scenario_a_formulas if f["is_pacemaker"]]
        if pacemakers:
            pm_match = sum(1 for f in pacemakers if f["pacemaker_matches"])
            print(f"    Pacemaker configs: {len(pacemakers)}, j*=10m⁻¹ mod 11 correct: {pm_match}/{len(pacemakers)}")
        # General mod p_b formula
        print(f"    j* ≡ 10m⁻¹ mod p_b: {formula_matches_mod_pb}/{formula_checked} ({100.0*formula_matches_mod_pb/formula_checked:.1f}%)")

        # Show bad_type distribution
        bad_types = Counter(f["bad_type"] for f in scenario_a_formulas)
        print(f"    Bad type: lower={bad_types['lower']}, upper={bad_types['upper']}")

        # Show j_star_mod_11 distribution — should always be in {1,...,10}
        j_mod11 = Counter(f["j_star_mod_11"] for f in scenario_a_formulas)
        print(f"    j* mod 11 distribution: {dict(sorted(j_mod11.items()))}")

        # Show m_mod_11 vs j_star_mod_11 relationship
        # In pacemaker: m*j* ≡ 10 (mod 11) always
        mjmod = Counter((f["m_mod_11"] * f["j_star_mod_11"]) % 11 for f in scenario_a_formulas)
        print(f"    m*j* mod 11 distribution: {dict(sorted(mjmod.items()))}")
        if len(mjmod) == 1:
            val = list(mjmod.keys())[0]
            print(f"    *** CONSTANT: m*j* ≡ {val} (mod 11) for ALL Scenario A configs! ***")

    return results


# ── detailed single-config display ────────────────────────────────────────────

def show_config_detail(speeds, n=11):
    """Detailed display for one config — residue table."""
    print(f"\n{'='*70}")
    print(f"DETAILED ANALYSIS: {tuple(speeds)}")
    print(f"{'='*70}")
    res = classify_mechanism(speeds, n=n, verbose=True)
    if res["scenario"] == "FAIL":
        print("  No witness/anchor found.")
        return

    witness_t = res["witness_t"]
    p_b = res["p_b"]
    j_star = res["j_star"]
    N = res["frame_size"]
    p_10 = speeds[-1]

    print(f"\n  Residue table: c * (11*{j_star}+1) mod {N}  for c in [1, {p_10}]")
    print(f"  Good zone: [{p_b}, {10*p_b}]   Bad zone: [0,{p_b}) ∪ ({10*p_b},{N})")
    print(f"  {'c':>4}  {'residue':>8}  {'zone':>6}  {'present':>8}")
    speed_set = set(speeds)
    for c in range(1, p_10 + 1):
        r = (c * (n * j_star + 1)) % N
        zone = "GOOD" if p_b <= r <= 10 * p_b else "BAD "
        present = "✓" if c in speed_set else " "
        marker = " ← ABSENT BAD" if (c not in speed_set and zone == "BAD ") else ""
        marker2 = " ← PRESENT BAD (!)" if (c in speed_set and zone == "BAD ") else ""
        print(f"  {c:>4}  {r:>8}  {zone:>6}  {present:>8}{marker}{marker2}")

    if res["scenario"] == "A":
        finfo = investigate_formula(speeds, res, n)
        if finfo:
            print(f"\n  Formula check (m={finfo['m']}, p_b={p_b}):")
            print(f"    m mod 11 = {finfo['m_mod_11']}")
            print(f"    j* = {j_star}")
            print(f"    j* mod 11 = {finfo['j_star_mod_11']}")
            print(f"    m * j* mod 11 = {(finfo['m_mod_11'] * finfo['j_star_mod_11']) % n}")
            print(f"    Bad type: {finfo['bad_type']}")
            if finfo["is_pacemaker"]:
                print(f"    Pacemaker formula j*=10m⁻¹ mod 11 = {finfo['pacemaker_formula_j']}: matches={finfo['pacemaker_matches']}")
            print(f"    General formula j*≡10m⁻¹ mod p_b={p_b}: {finfo['formula_j_mod_pb']}, j* mod p_b={finfo['j_star_mod_pb']}, matches={finfo['formula_matches_mod_pb']}")


# ── main ──────────────────────────────────────────────────────────────────────

def main():
    n = 11
    print("=" * 70)
    print("LRC WITNESS MECHANISM ANALYSIS  |  n=11  |  Missing Complement Hypothesis")
    print("=" * 70)

    all_results = []

    # ── Type B: adversarial configs ──
    type_b = generate_type_b()
    b_items = [(sp, lbl) for sp, lbl in type_b if sp[-1] / sp[0] > 10]
    res_b = batch_mechanism_analysis(b_items, label="TYPE B: Adversarial configs", verbose_first=3)
    all_results.extend(res_b)

    # ── Type C: near-boundary ──
    type_c = generate_type_c()
    c_items = [(sp, lbl) for sp, lbl in type_c if sp[-1] / sp[0] > 10]
    res_c = batch_mechanism_analysis(c_items, label="TYPE C: Near-boundary configs", verbose_first=3)
    all_results.extend(res_c)

    # ── Type A: 1000 random configs ──
    type_a = generate_type_a(1000, seed=42)
    res_a = batch_mechanism_analysis(type_a, label="TYPE A: 1000 random configs (seed=42)", verbose_first=2)
    all_results.extend(res_a)

    # ── Global summary ──
    print("\n" + "=" * 70)
    print("GLOBAL SUMMARY")
    print("=" * 70)
    total = len(all_results)
    sc_counts = Counter(r["scenario"] for r in all_results)
    abd_dist = Counter(r["absent_bad_count"] for r in all_results if r["absent_bad_count"] >= 0)

    print(f"Total configs: {total}")
    print("\nScenario distribution (global):")
    for sc, cnt in sorted(sc_counts.items()):
        pct = 100.0 * cnt / total if total else 0
        print(f"  {sc}: {cnt} ({pct:.1f}%)")

    print("\nabsent_bad_count distribution (global):")
    for k in sorted(abd_dist.keys()):
        pct = 100.0 * abd_dist[k] / total if total else 0
        print(f"  {k}: {abd_dist[k]} ({pct:.1f}%)")

    # Missing complement hypothesis verdict
    fail_count = sc_counts.get("FAIL", 0) + sc_counts.get("SANITY_FAIL", 0)
    scenario_c_count = sc_counts.get("C", 0)
    print(f"\nMissing Complement Hypothesis (absent_bad >= 1 for all configs):")
    if scenario_c_count == 0 and fail_count == 0:
        print("  ✓ CONFIRMED: Every witness has at least one absent bad integer.")
    elif scenario_c_count > 0:
        print(f"  ✗ COUNTEREXAMPLE: {scenario_c_count} configs have absent_bad=0 (Scenario C).")
    if fail_count > 0:
        print(f"  WARNING: {fail_count} configs had no witness or no anchor found.")

    # Tight hypothesis: always exactly 1
    scenario_b_count = sc_counts.get("B", 0)
    scenario_a_count = sc_counts.get("A", 0)
    print(f"\nTight Missing Complement Hypothesis (absent_bad == 1 for all):")
    if scenario_b_count == 0 and scenario_c_count == 0 and fail_count == 0:
        print("  ✓ CONFIRMED: Every witness has EXACTLY one absent bad integer (Scenario A).")
        print("  → UNIFIED CLOSED-FORM PROOF IS POSSIBLE.")
    else:
        print(f"  Not tight: A={scenario_a_count}, B={scenario_b_count}, C={scenario_c_count}")

    # m*j* mod 11 constant?
    scenario_a_results = [r for r in all_results if r["scenario"] == "A"]
    if scenario_a_results:
        mjmod_vals = set()
        for r in scenario_a_results:
            m = r["absent_bad"][0]
            j = r["j_star"]
            mjmod_vals.add((m * j) % n)
        print(f"\nFor Scenario A configs: m*j* mod 11 values = {mjmod_vals}")
        if len(mjmod_vals) == 1:
            print(f"  ✓ CONSTANT: m*j* ≡ {list(mjmod_vals)[0]} (mod 11) for ALL Scenario A configs")
            print(f"  → This generalizes j* = 10m⁻¹ mod 11 to ALL Case R> configs!")

    # Show a few detailed examples for interesting cases
    print("\n" + "=" * 70)
    print("DETAILED EXAMPLES")
    print("=" * 70)

    # Pacemaker example
    print("\n--- Pacemaker (ratio=11) ---")
    pm_config = [1, 4, 5, 6, 7, 8, 9, 10, 11, 11]
    # find a proper pacemaker config
    pm_config = [1, 2, 3, 4, 5, 7, 8, 9, 10, 11]  # missing 6
    show_config_detail(pm_config, n=n)

    # Non-pacemaker from Type B
    print("\n--- Non-pacemaker (Type B adversarial) ---")
    show_config_detail([1, 4, 7, 9, 11, 12, 14, 15, 16, 20], n=n)

    # Near-boundary
    print("\n--- Near-boundary ratio=11 ---")
    show_config_detail([1, 2, 3, 4, 5, 6, 7, 8, 9, 11], n=n)

    # Find a Scenario B config if any
    sc_b_examples = [r for r in all_results if r["scenario"] == "B"]
    if sc_b_examples:
        print(f"\n--- Scenario B example (absent_bad > 1) ---")
        # Find corresponding speeds
        # We'd need to store speeds in results — let's just note them
        print(f"  Found {len(sc_b_examples)} Scenario B configs. First absent_bad list:")
        for r in sc_b_examples[:3]:
            print(f"    absent_bad={r['absent_bad']}, p_b={r['p_b']}, j*={r['j_star']}")

    sc_c_examples = [r for r in all_results if r["scenario"] == "C"]
    if sc_c_examples:
        print(f"\n--- Scenario C example (absent_bad = 0, self-contained) ---")
        print(f"  Found {len(sc_c_examples)} Scenario C configs.")
        for r in sc_c_examples[:3]:
            print(f"    p_b={r['p_b']}, j*={r['j_star']}, anchor_frame={r['frame_size']}")


if __name__ == "__main__":
    main()
