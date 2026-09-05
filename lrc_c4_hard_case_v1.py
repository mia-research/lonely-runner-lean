#!/usr/bin/env python3
"""
LRC n=11 Hard Case Investigation: Corridor C4
==============================================
Corridor C4 = (1/5, 1/4), x = e1*t, released labels {5,...,10}.
For 9 runners with ratios lambda_i = v_i/v_1 (rational), we ask:
can all 6 labels be covered for ALL x in C4?

Investigation goals:
1. Verify the v1=7, vA=45, vB=69 counterexample structure
2. Find the "hardest" configurations (max coverage on C4)
3. Identify where lonely times occur in hard configurations
4. Understand the cascade synchronization structure
"""

import numpy as np
from fractions import Fraction
import itertools
from collections import defaultdict, Counter
import sys

# ─── Core primitives ───────────────────────────────────────────────────────────

def F(y):
    """Folded map: F(y) = min(y mod 11, 11 - y mod 11)"""
    r = y % 11.0
    return r if r <= 5.5 else 11.0 - r

def service_set_float(a):
    """Which of {5,...,10} does a runner at folded speed 'a' cover?"""
    covered = set()
    for m in range(5, 11):
        frac = (a * m / 11.0) % 1.0
        if frac < 1.0/11 or frac > 10.0/11:
            covered.add(m)
    return covered

def coverage_at_x(x, lambdas):
    """Union of service sets for all runners at position x in C4."""
    covered = set()
    for lam in lambdas:
        a = F(lam * x)
        covered |= service_set_float(a)
    return covered

def scan_C4(lambdas, n_points=50000):
    """
    Scan C4 = (1/5, 1/4) for coverage failures.
    Returns dict with:
      min_cov: minimum |coverage| found
      worst_x: x where coverage is worst
      uncovered: labels uncovered at worst_x
      gap_measure: fraction of C4 where coverage < 6
      gap_by_label: for each label, fraction of C4 where it's uncovered
    """
    xs = np.linspace(0.2 + 1e-8, 0.25 - 1e-8, n_points)
    min_cov = 6
    worst_x = None
    uncovered_worst = set()
    gap_count = 0
    label_miss = defaultdict(int)

    for x in xs:
        cov = coverage_at_x(x, lambdas)
        missing = {5,6,7,8,9,10} - cov
        if missing:
            gap_count += 1
            for m in missing:
                label_miss[m] += 1
            if len(cov) < min_cov:
                min_cov = len(cov)
                worst_x = x
                uncovered_worst = missing

    return {
        'min_cov': min_cov,
        'worst_x': worst_x,
        'uncovered': uncovered_worst,
        'gap_fraction': gap_count / n_points,
        'gap_by_label': {m: label_miss[m]/n_points for m in range(5,11)},
        'full_coverage': (gap_count == 0),
    }

# ─── Part 1: Verify the counterexample structure ───────────────────────────────

def part1_verify_counterexample():
    print("=" * 70)
    print("PART 1: Counterexample structure verification")
    print("v1=7, vA=45, vB=69 with various completions")
    print("=" * 70)

    v1 = 7
    core = [45, 69]  # the synchronized pair
    core_lam = [v/v1 for v in core]

    # Check what each core runner covers at x=7/30
    x_star = Fraction(7, 30)
    x_float = float(x_star)
    print(f"\nSynchronization point x* = 7/30 = {x_float:.6f}  (C4 = (0.2, 0.25))")
    print(f"  F(λA * x*) = F({45}/{7} * 7/30) = F({45*7}/{7*30}) = F({45}/30) = F(1.5) = {F(1.5):.4f}")
    print(f"  F(λB * x*) = F({69}/{7} * 7/30) = F({69}/30) = F(2.3) = {F(2.3):.4f}")
    print(f"  → At x*, runner A exits P4={{7,8}} at boundary a=3/2")
    print(f"    runner B exits P6={{5,10}} at boundary a=23/10")
    print(f"  → Labels 8 and 10 BOTH dropped at x*")

    # What single runners cover at x_star (before and after)
    eps = 1e-6
    print(f"\n  Coverage just before x* (x={x_float-eps:.8f}):")
    a_A = F((45/7) * (x_float - eps))
    a_B = F((69/7) * (x_float - eps))
    print(f"    Runner A: a={a_A:.4f}, S={service_set_float(a_A)}")
    print(f"    Runner B: a={a_B:.4f}, S={service_set_float(a_B)}")

    print(f"\n  Coverage just after x* (x={x_float+eps:.8f}):")
    a_A = F((45/7) * (x_float + eps))
    a_B = F((69/7) * (x_float + eps))
    print(f"    Runner A: a={a_A:.4f}, S={service_set_float(a_A)}")
    print(f"    Runner B: a={a_B:.4f}, S={service_set_float(a_B)}")

    # Find what runners would need to be at x* to cover {8} and {10}
    print(f"\n  Runners needed at x* to cover label 8 (via P10={{5,8}} or P3={{8,9}} etc):")
    for v_test in range(50, 200):
        lam = v_test / v1
        a = F(lam * x_float)
        s = service_set_float(a)
        if 8 in s:
            print(f"    v={v_test} → λ={lam:.4f}, a=F(λx*)={a:.4f}, S={sorted(s)}")
            if v_test > 140: break

    print(f"\n  Runners needed at x* to cover label 10 (via P8={{7,10}} etc):")
    for v_test in range(50, 200):
        lam = v_test / v1
        a = F(lam * x_float)
        s = service_set_float(a)
        if 10 in s and 8 not in s:
            print(f"    v={v_test} → λ={lam:.4f}, a=F(λx*)={a:.4f}, S={sorted(s)}")
            if v_test > 140: break

    # Now test: does the "minimal 5-runner core" fail in C4?
    print(f"\n  Testing 5-runner core {{45,69}} + {{7}} (only core runners, v1=7):")
    lams_5 = [45/7, 69/7]
    res = scan_C4(lams_5)
    print(f"    Gap fraction: {res['gap_fraction']:.4f}")
    print(f"    Min coverage: {res['min_cov']} at x≈{res['worst_x']:.6f}")
    print(f"    Missing labels: {sorted(res['uncovered'])}")

# ─── Part 2: Cascade synchronization: how many runners does it take? ──────────

def part2_cascade_analysis():
    print("\n" + "=" * 70)
    print("PART 2: Cascade analysis — minimum runners for full C4 coverage")
    print("Starting from v1=7, vA=45, vB=69 and adding runners greedily")
    print("=" * 70)

    v1 = 7
    # Base runners
    speeds = [45, 69]
    lambdas = [v/v1 for v in speeds]

    # Greedily add runners that maximally reduce the gap fraction
    candidate_range = list(range(8, 300))
    candidate_range = [v for v in candidate_range if v % v1 != 0 or v == v1]

    print(f"\nGreedy runner addition (v1={v1}, base speeds={speeds}):")
    for step in range(9):  # max 9 more runners
        res_base = scan_C4(lambdas, n_points=20000)
        if res_base['full_coverage']:
            print(f"  Step {step}: FULL COVERAGE ACHIEVED with {len(speeds)} runners!")
            print(f"  Speeds: {speeds}")
            break

        best_v = None
        best_gap = res_base['gap_fraction']
        best_res = res_base

        for v in candidate_range:
            if v in speeds:
                continue
            test_lam = lambdas + [v/v1]
            res = scan_C4(test_lam, n_points=5000)
            if res['gap_fraction'] < best_gap:
                best_gap = res['gap_fraction']
                best_v = v
                best_res = res

        if best_v is None:
            print(f"  Step {step}: No improvement possible. Gap stuck at {res_base['gap_fraction']:.4f}")
            break

        speeds.append(best_v)
        lambdas.append(best_v/v1)
        print(f"  Step {step+1}: Add v={best_v} (λ={best_v/v1:.4f}) → gap={best_gap:.6f}, "
              f"min_cov={best_res['min_cov']}, missing={sorted(best_res['uncovered'])}")
        print(f"    Current speeds: {speeds}")

        if len(speeds) == 9:
            final = scan_C4(lambdas, n_points=50000)
            print(f"\n  FINAL (9 runners): gap={final['gap_fraction']:.6f}, "
                  f"full_coverage={final['full_coverage']}")
            print(f"  Gap by label: {dict(sorted(final['gap_by_label'].items()))}")
            if not final['full_coverage']:
                print(f"  Lonely time found at x≈{final['worst_x']:.8f}, missing={sorted(final['uncovered'])}")
            break

# ─── Part 3: Systematic search — which v1 values are hardest? ─────────────────

def part3_systematic_by_v1():
    print("\n" + "=" * 70)
    print("PART 3: Systematic search by v1 — hardest base speeds")
    print("=" * 70)

    results = []
    for v1 in range(1, 30):
        # Generate candidate speeds: v1+1 through v1*30, exclude multiples of... nothing
        # Actually all distinct integers > v1
        candidates = list(range(v1+1, v1*25+1))

        # Try many random 9-runner configurations
        best_gap_frac = 1.0
        best_speeds = None
        rng = np.random.default_rng(seed=v1*42)

        n_trials = 200
        for _ in range(n_trials):
            chosen = sorted(rng.choice(candidates, size=9, replace=False).tolist())
            lams = [v/v1 for v in chosen]
            res = scan_C4(lams, n_points=2000)
            if res['gap_fraction'] < best_gap_frac:
                best_gap_frac = res['gap_fraction']
                best_speeds = chosen
                if best_gap_frac == 0.0:
                    break

        results.append((v1, best_gap_frac, best_speeds))
        marker = " ← FULL COVERAGE" if best_gap_frac == 0.0 else ""
        print(f"  v1={v1:3d}: best_gap={best_gap_frac:.4f}  speeds={best_speeds}{marker}")

    # Find hardest cases (smallest gap fraction)
    results.sort(key=lambda r: r[1])
    print(f"\n  Top 10 hardest v1 values (smallest gap fraction found):")
    for v1, gap, speeds in results[:10]:
        print(f"    v1={v1}: gap={gap:.6f}, speeds={speeds}")

# ─── Part 4: Characterize the hard configurations' lonely time locations ───────

def part4_lonely_time_location():
    print("\n" + "=" * 70)
    print("PART 4: Hard configurations — lonely time characterization")
    print("Where in C4 does the lonely time occur?")
    print("=" * 70)

    # Test specific structured configurations
    test_cases = [
        # (v1, [v2,...,v10], description)
        (1,  [2,3,4,5,6,7,8,9,10], "AP speeds 1..10"),
        (1,  [2,3,4,5,6,7,8,9,11], "AP with 11 instead of 10"),
        (7,  [8,9,10,11,12,13,14,15,16], "v1=7, AP+7"),
        (7,  [45,69,98,127,160,190,220,250,280], "v1=7 + cascade attempt"),
        (2,  [3,5,7,11,13,17,19,23,29], "v1=2, first 9 odd primes"),
        (1,  [3,5,7,11,13,17,19,23,29], "v1=1, 9 primes"),
        (11, [12,13,14,15,16,17,18,19,20], "v1=11, consecutive"),
        (6,  [7,8,9,10,11,12,13,14,15], "v1=6, consecutive"),
    ]

    for v1, others, desc in test_cases:
        lams = [v/v1 for v in others]
        res = scan_C4(lams, n_points=100000)

        print(f"\n  [{desc}]")
        print(f"  Speeds: v1={v1}, others={others}")
        if res['full_coverage']:
            print(f"  ⚠️  FULL COVERAGE on C4 — no lonely time in C4 corridor!")
        else:
            print(f"  Gap fraction: {res['gap_fraction']:.6f}  ({res['gap_fraction']*100:.3f}% of C4)")
            print(f"  Min coverage: {res['min_cov']} labels (missing: {sorted(res['uncovered'])})")
            print(f"  Worst x: {res['worst_x']:.8f}")
            print(f"  t* = m*·x*/(11·v1) for m* ∈ {sorted(res['uncovered'])}, x*≈{res['worst_x']:.6f}")
            # Show gap by label
            by_label = {m: f"{v*100:.3f}%" for m,v in sorted(res['gap_by_label'].items()) if v > 0}
            print(f"  Uncovered fraction by label: {by_label}")

# ─── Part 5: Can ANY 9-runner config achieve full coverage on C4? ──────────────

def part5_full_coverage_search():
    print("\n" + "=" * 70)
    print("PART 5: Exhaustive search — can 9 runners fully cover C4?")
    print("(If yes: we need a different argument. If no: LRC provable here.)")
    print("=" * 70)

    full_coverage_found = False

    # Strategy: for each v1, find the best 9-runner config
    for v1 in range(1, 15):
        rng = np.random.default_rng(seed=12345 + v1)
        candidates = list(range(v1+1, v1*50+1))

        n_trials = 500
        best_gap = 1.0
        best_config = None

        for trial in range(n_trials):
            chosen = sorted(rng.choice(candidates, size=9, replace=False).tolist())
            lams = [v/v1 for v in chosen]
            res = scan_C4(lams, n_points=5000)
            if res['gap_fraction'] < best_gap:
                best_gap = res['gap_fraction']
                best_config = (v1, chosen, res)
            if best_gap == 0.0:
                break

        v1_, speeds, res = best_config
        if res['full_coverage']:
            print(f"  *** FULL COVERAGE FOUND: v1={v1}, speeds={speeds} ***")
            full_coverage_found = True
            # Verify with finer grid
            lams = [v/v1 for v in speeds]
            fine = scan_C4(lams, n_points=500000)
            print(f"  Fine-grid verification (500k points): full_coverage={fine['full_coverage']}")
            if not fine['full_coverage']:
                print(f"  Actually gap={fine['gap_fraction']:.8f} at x={fine['worst_x']:.10f}")
                print(f"  Missing: {sorted(fine['uncovered'])}")
        else:
            print(f"  v1={v1:3d}: best gap={best_gap:.6f}, speeds={speeds}")

    if not full_coverage_found:
        print(f"\n  No full-coverage configuration found in search.")
        print(f"  (This is evidence — but not proof — that full coverage is impossible.)")

# ─── Part 6: Analyze the synchronization cascade depth ────────────────────────

def part6_cascade_depth():
    print("\n" + "=" * 70)
    print("PART 6: Synchronization cascade — how many simultaneous exits needed?")
    print("=" * 70)

    v1 = 7
    # The base transition: vA=45 exits P4, vB=69 exits P6 at x=7/30
    x_sync1 = 7/30

    print(f"Level 1 synchronization at x={x_sync1:.6f}:")
    print(f"  vA=45 exits P4={{7,8}}: labels 8 lost")
    print(f"  vB=69 exits P6={{5,10}}: labels 10 lost")
    print(f"  Need: runners entering P8={{7,10}} and P10={{5,8}} at x=7/30")

    # Find level-2 runners
    print(f"\nLevel 2: what enters P8={{7,10}} and P10={{5,8}} at x=7/30?")

    p8_range = (16/5, 23/7)  # = (3.2, 3.2857)
    p10_range = (21/5, 17/4)  # = (4.2, 4.25)

    # For runner v_D to enter P8 at x=7/30 from the LEFT (i.e., it's just entering P8):
    # F(λ_D * 7/30) ∈ (16/5, 23/7)
    # λ_D * 7/30 ∈ (16/5, 23/7) [forward]
    # λ_D ∈ (16/5 * 30/7, 23/7 * 30/7) = (96/7, 690/49) = (13.71, 14.08)

    print(f"\n  Runners entering P8 at x=7/30 (need λ ∈ (13.71, 14.08)):")
    for v in range(80, 120):
        lam = v / v1
        if 13.71 < lam < 14.08:
            a = F(lam * x_sync1)
            s = service_set_float(a)
            print(f"    v={v}: λ={lam:.4f}, a={a:.4f}, S={sorted(s)}")

    print(f"\n  Runners entering P10 at x=7/30 (need λ ∈ (18.0, 18.21)):")
    for v in range(100, 150):
        lam = v / v1
        if 18.0 < lam < 18.21:
            a = F(lam * x_sync1)
            s = service_set_float(a)
            print(f"    v={v}: λ={lam:.4f}, a={a:.4f}, S={sorted(s)}")

    # Now: if we add these level-2 runners, what happens AFTER x=7/30?
    print(f"\n  Level-2 transition: vA=45, vB=69, vD=98(P8), vE=127(P10)...")

    # Check if vD=98 enters P8 at 7/30
    lam_D = 98/7
    a_D = F(lam_D * x_sync1)
    print(f"  vD=98: λ={lam_D:.4f}, a at x*={a_D:.4f}, S={sorted(service_set_float(a_D))}")

    lam_E = 127/7
    a_E = F(lam_E * x_sync1)
    print(f"  vE=127: λ={lam_E:.4f}, a at x*={a_E:.4f}, S={sorted(service_set_float(a_E))}")

    # Scan C4 with this 4-runner core + runner C for P9
    # P9 = {6,9} needs λ ∈ (14.22, 18.89)
    print(f"\n  Finding runner for P9={{6,9}}...")
    p9_range = (32/9, 34/9)  # = (3.556, 3.778)
    for v in range(100, 160):
        lam = v / v1
        # Needs to be active in P9 for some x in C4
        # λ in (128/9, 170/9) = (14.22, 18.89)
        if 14.22 < lam < 18.89:
            a = F(lam * x_sync1)
            s = service_set_float(a)
            if 6 in s and 9 in s:
                print(f"    v={v}: λ={lam:.4f}, a at x*={a:.4f}, S={sorted(s)} ← P9 active at x*")

    # Full 5-runner test: vA=45, vB=69, vD=98, vE=127 + one P9 runner
    for v_C9 in [105, 112, 119, 126, 133]:
        speeds_5 = [45, 69, 98, 127, v_C9]
        lams_5 = [v/v1 for v in speeds_5]
        res = scan_C4(lams_5, n_points=20000)
        print(f"  5 runners {speeds_5}: gap={res['gap_fraction']:.4f}, "
              f"min_cov={res['min_cov']}, missing={sorted(res['uncovered'])}")

# ─── Part 7: Label-by-label hardness ──────────────────────────────────────────

def part7_per_label_hardness():
    print("\n" + "=" * 70)
    print("PART 7: Per-label coverage analysis — which label is hardest to cover?")
    print("=" * 70)

    v1 = 1
    rng = np.random.default_rng(42)

    # For many random 9-runner configs, track which label fails most
    label_fail_count = Counter()
    n_configs = 2000

    for _ in range(n_configs):
        others = sorted(rng.choice(range(2, 150), size=9, replace=False).tolist())
        lams = [v/v1 for v in others]
        res = scan_C4(lams, n_points=1000)
        for m in res['uncovered']:
            label_fail_count[m] += 1

    print(f"  Over {n_configs} random configs (v1=1, speeds from 2..149):")
    print(f"  Label fail counts: {dict(sorted(label_fail_count.items()))}")
    total = sum(label_fail_count.values())
    print(f"  Relative: {dict((m, f'{c/total:.3f}') for m,c in sorted(label_fail_count.items()))}")

    # Repeat for v1=7
    label_fail_v7 = Counter()
    for _ in range(n_configs):
        v1_t = 7
        others = sorted(rng.choice(range(8, 200), size=9, replace=False).tolist())
        lams = [v/v1_t for v in others]
        res = scan_C4(lams, n_points=1000)
        for m in res['uncovered']:
            label_fail_v7[m] += 1

    print(f"\n  Over {n_configs} random configs (v1=7, speeds from 8..199):")
    total_v7 = sum(label_fail_v7.values())
    print(f"  Label fail counts: {dict(sorted(label_fail_v7.items()))}")
    if total_v7 > 0:
        print(f"  Relative: {dict((m, f'{c/total_v7:.3f}') for m,c in sorted(label_fail_v7.items()))}")

# ─── Part 8: Distribution of lonely time x* ───────────────────────────────────

def part8_lonely_time_distribution():
    print("\n" + "=" * 70)
    print("PART 8: Distribution of lonely times within C4")
    print("=" * 70)

    rng = np.random.default_rng(999)
    lonely_xs = []
    label_at_lonely = Counter()

    n_configs = 3000
    for _ in range(n_configs):
        v1 = rng.integers(1, 20)
        others = sorted(rng.choice(range(int(v1)+1, int(v1)*40+1), size=9, replace=False).tolist())
        lams = [v/v1 for v in others]
        res = scan_C4(lams, n_points=2000)
        if res['worst_x'] is not None:
            lonely_xs.append(res['worst_x'])
            for m in res['uncovered']:
                label_at_lonely[m] += 1

    if lonely_xs:
        xs_arr = np.array(lonely_xs)
        c4_width = 0.25 - 0.2
        # Normalize to [0,1] within C4
        xs_norm = (xs_arr - 0.2) / c4_width

        print(f"  Over {n_configs} configs, lonely times found in {len(lonely_xs)} cases")
        print(f"  Distribution within C4 (0=left edge 1/5, 1=right edge 1/4):")
        bins = np.linspace(0, 1, 11)
        hist, _ = np.histogram(xs_norm, bins=bins)
        for i, (lo, hi) in enumerate(zip(bins[:-1], bins[1:])):
            bar = "█" * (hist[i] // 20)
            print(f"    [{lo:.1f},{hi:.1f}]: {hist[i]:5d}  {bar}")

        print(f"\n  Most common uncovered label at lonely time:")
        total_l = sum(label_at_lonely.values())
        for m, cnt in sorted(label_at_lonely.items(), key=lambda x: -x[1]):
            print(f"    Label {m}: {cnt} times ({100*cnt/total_l:.1f}%)")

# ─── Main ──────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="LRC C4 Hard Case Investigation")
    parser.add_argument("--part", type=int, default=0, help="Which part to run (0=all)")
    args = parser.parse_args()

    if args.part in (0, 1): part1_verify_counterexample()
    if args.part in (0, 2): part2_cascade_analysis()
    if args.part in (0, 3): part3_systematic_by_v1()
    if args.part in (0, 4): part4_lonely_time_location()
    if args.part in (0, 5): part5_full_coverage_search()
    if args.part in (0, 6): part6_cascade_depth()
    if args.part in (0, 7): part7_per_label_hardness()
    if args.part in (0, 8): part8_lonely_time_distribution()
