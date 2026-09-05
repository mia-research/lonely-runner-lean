#!/usr/bin/env python3
"""
Case B Pattern Analysis — Theorem 12.1 Case B
==============================================
Reads harness output and extracts geometric patterns in safe times.

Focuses on three-speed structure at safe times:
  - Class D (divisible): q_j * n  — positions mod 1
  - Class R (dropped):   d_1, d_2 — distances (should be >= 1/n; dropped so irrelevant)
  - Class U (retained):  pure residues — spread across circle

Key hypotheses to test:
  H1: Divisible runners always land AWAY from 0 at safe times (distance ≥ X)
  H2: Safe times t satisfy t ∈ [k/q, (k+1)/q) for some Bertrand prime q
  H3: Three-class geometric obstruction — divisible and dropped runners
      "compete" for the same arc, forcing a safe gap in retained coverage
"""

from math import gcd, isqrt
from fractions import Fraction
from collections import defaultdict
import json, sys, os

# ─── load results ──────────────────────────────────────────────────────────

def load_results(path):
    with open(path) as f:
        return json.load(f)

# ─── helpers ───────────────────────────────────────────────────────────────

def is_prime(n):
    if n < 2: return False
    if n == 2: return True
    if n % 2 == 0: return False
    for i in range(3, isqrt(n) + 1, 2):
        if n % i == 0: return False
    return True

def prime_factors(n):
    factors = []
    d, m = 2, n
    while d * d <= m:
        if m % d == 0:
            factors.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        factors.append(m)
    return factors

def best_rational(x, max_denom=2000):
    """Return (p, q) s.t. p/q ≈ x with q ≤ max_denom, minimising |x - p/q|."""
    f = Fraction(x).limit_denominator(max_denom)
    return f.numerator, f.denominator

# ─── hypothesis tests ──────────────────────────────────────────────────────

def test_H1_divisible_distance(results):
    """
    H1: At every safe time, each divisible runner has distance ≥ some threshold X(n).
    Empirically find X(n) = min over all safe times and all div runners of dist.
    """
    print("\n── H1: Divisible runner minimum distance at safe times ──")
    by_n = defaultdict(list)
    for r in results:
        if r['avg_div_min_dist'] > 0:
            by_n[r['n']].append(r['avg_div_min_dist'])

    for n in sorted(by_n):
        vals = by_n[n]
        min_d = min(vals)
        expected = 1/n
        print(f"  n={n:3d}: min_avg_div_dist = {min_d:.5f}  (1/n = {expected:.5f})  "
              f"ratio = {min_d/expected:.3f}  {'✓ ≥ 1/n' if min_d >= expected else '✗ < 1/n'}")

    # Global: does divisible runner ALWAYS have dist ≥ 1/n at safe time?
    all_min = [r['avg_div_min_dist'] for r in results if r['avg_div_min_dist'] > 0]
    if all_min:
        global_min = min(all_min)
        print(f"\n  Global minimum avg div dist: {global_min:.5f}")
        print(f"  Interpretation: divisible runners have avg dist ≥ {global_min:.4f} at safe times")

def test_H2_bertrand_structure(results):
    """
    H2: For each tuple, some Bertrand prime q ∈ (n, 2n) gives a working witness.
    Also check: does first_safe time have small denominator (Bertrand-type)?
    """
    print("\n── H2: Bertrand prime witness coverage ──")
    by_n = defaultdict(lambda: {'total': 0, 'bertrand': 0, 'fails': []})
    for r in results:
        n = r['n']
        by_n[n]['total'] += 1
        if r['bertrand_works']:
            by_n[n]['bertrand'] += 1
        else:
            by_n[n]['fails'].append((r['d1'], r['d2'], r['div_speeds']))

    for n in sorted(by_n):
        s = by_n[n]
        rate = s['bertrand'] / s['total'] * 100 if s['total'] else 0
        status = 'universal' if rate == 100 else f'{len(s["fails"])} fails'
        print(f"  n={n:3d}: {s['bertrand']:3d}/{s['total']:3d} ({rate:5.1f}%)  {status}")
        if s['fails']:
            for fail in s['fails'][:3]:
                print(f"         ↳ d=({fail[0]},{fail[1]}), div={fail[2]}")

def test_H3_three_class_structure(results):
    """
    H3: Geometric structure — at safe times:
    - dropped runners d1, d2 have distance << 1/n? No — they're dropped, irrelevant.
    - Actually H3: retained runners all have dist ≥ 1/n AND divisible have dist ≥ 1/n.
      The "forced gap" must come from the interaction of the three classes.

    Check: is there a pattern in (divisible position, dropped position) space?
    """
    print("\n── H3: Three-class geometric structure ──")

    # For each result, look at features_sample (if present)
    # Since we saved without features_sample in JSON, we'll do coarse analysis
    # using witness_types and first_safe

    # Check: first_safe always < 1/n ?
    first_safe_below_1n = sum(1 for r in results
                               if r['first_safe'] and r['first_safe'] < 1/r['n'])
    total_with_safe = sum(1 for r in results if r['first_safe'] is not None)
    print(f"  first_safe < 1/n: {first_safe_below_1n}/{total_with_safe}")

    # What are the common first-safe denominators?
    denom_counts = defaultdict(int)
    for r in results:
        if r['first_safe']:
            f = Fraction(r['first_safe']).limit_denominator(5000)
            n = r['n']
            rel = f.denominator / n
            denom_counts[f.denominator] += 1

    print(f"\n  Top 20 first-safe denominators:")
    for d, cnt in sorted(denom_counts.items(), key=lambda x: -x[1])[:20]:
        is_p = '(prime)' if is_prime(d) else ''
        print(f"    denom={d:6d} {is_p:8s}: {cnt:3d} tuples")

def test_witness_type_by_config(results):
    """
    Does witness type depend on div-speed configuration (small q vs large q)?
    """
    print("\n── Witness type vs. divisible speed configuration ──")
    by_config = defaultdict(lambda: defaultdict(int))
    for r in results:
        label = r.get('label', '')
        # Extract config name
        parts = label.split(']')
        config = parts[-1].strip() if len(parts) > 1 else 'unknown'
        for wt, cnt in r['witness_types'].items():
            by_config[config][wt] += cnt

    for config in sorted(by_config.keys()):
        wts = by_config[config]
        total = sum(wts.values())
        print(f"  {config:20s}: "
              + "  ".join(f"{wt}={cnt}" for wt, cnt in sorted(wts.items())))

def test_divisible_position_at_safe_times(results):
    """
    Extract: where do divisible runners sit on [0,1) at safe times?
    Hypothesis: they concentrate near 1/(2n), ..., (2n-1)/(2n) (far from 0 and 1).
    """
    print("\n── Divisible runner position at safe times ──")

    # Group by pair_type
    by_type = defaultdict(lambda: {'near_0': 0, 'mid': 0, 'total': 0})
    for r in results:
        pt = r.get('pair_type', 'unknown')
        n = r['n']
        if r['avg_div_min_dist'] > 0:
            dist = r['avg_div_min_dist']
            by_type[pt]['total'] += 1
            if dist < 1/(2*n):
                by_type[pt]['near_0'] += 1
            else:
                by_type[pt]['mid'] += 1

    for pt, stats in sorted(by_type.items()):
        if stats['total'] > 0:
            print(f"  {pt:15s}: near_0={stats['near_0']:3d}  mid={stats['mid']:3d}  "
                  f"total={stats['total']:3d}")

def test_period_structure(results):
    """
    Check: does first_safe = k/q for small prime q?
    If so, what is q relative to n and div_speeds?
    """
    print("\n── Period structure of first safe time ──")

    hits = defaultdict(int)  # rel-denom → count
    n_values_seen = sorted(set(r['n'] for r in results))

    for n in n_values_seen:
        pf = prime_factors(n)
        n_results = [r for r in results if r['n'] == n and r['first_safe']]
        if not n_results:
            continue

        print(f"\n  n={n} (factors {pf}):")
        for r in n_results[:6]:  # sample
            t = Fraction(r['first_safe']).limit_denominator(10000)
            p_val, q_val = t.numerator, t.denominator
            rel = f"{p_val}/{q_val}"
            div_max = max(r['div_speeds']) if r['div_speeds'] else 0
            print(f"    d=({r['d1']},{r['d2']}) div={r['div_speeds'][:2]}: "
                  f"first_safe≈{rel}  denom={q_val}  prime?{is_prime(q_val)}  "
                  f"denom/n={q_val/n:.2f}")

def check_lrc_universal(results):
    """Check that LRC holds for all tested configurations."""
    fails = [r for r in results if not r['lrc_holds']]
    print(f"\n── LRC Universality Check ──")
    print(f"  Total tested: {len(results)}")
    print(f"  LRC holds:    {len(results) - len(fails)}")
    print(f"  LRC FAILS:    {len(fails)}")
    if fails:
        for f in fails:
            print(f"  *** FAIL: n={f['n']}, d=({f['d1']},{f['d2']}), "
                  f"div={f['div_speeds']}, label={f['label']} ***")
    return len(fails) == 0


# ─── main ─────────────────────────────────────────────────────────────────

def main():
    results_path = "/Users/trentpalelei/Desktop/Math Ex/reports/case_b_harness_results.json"
    if not os.path.exists(results_path):
        print(f"Results file not found: {results_path}")
        print("Run case_b_empirical_harness.py first.")
        sys.exit(1)

    results = load_results(results_path)
    print(f"Loaded {len(results)} configurations.")

    universal = check_lrc_universal(results)
    test_H1_divisible_distance(results)
    test_H2_bertrand_structure(results)
    test_H3_three_class_structure(results)
    test_witness_type_by_config(results)
    test_divisible_position_at_safe_times(results)
    test_period_structure(results)

    print(f"\n{'='*60}")
    print("CONCLUSION:")
    if not universal:
        print("  *** LRC FAILS for some tuple — CRITICAL ERROR ***")
    else:
        print("  LRC holds universally for all tested configurations.")

    # Identify strongest pattern
    print("\nStrongest pattern candidates:")
    print("  [See above — look for near-100% Bertrand rate and consistent denom structure]")

if __name__ == '__main__':
    main()
