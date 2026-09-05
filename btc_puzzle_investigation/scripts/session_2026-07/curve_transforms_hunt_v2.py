#!/usr/bin/env python3
"""
Curve-transforms leak hunt V2: Same as V1, but with:
1. Larger feature set (second-order combos included)
2. More aggressive filtering: check top 500 raw MI pairs
3. Explicit analysis of candidates with adj_mi > 0.001
4. Better reporting of near-misses
"""
import sys
sys.path.insert(0, '/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/scripts/session_2026-07')

import leak_lib as L
import numpy as np

def build_comprehensive_features(d):
    """
    Build comprehensive feature dict from curve transforms of (X,Y).
    Includes first-order transforms and selected second-order combos.
    """
    X, Y = d['X'], d['Y']
    N = d['N']
    features = {}

    # === Primary curve transforms ===
    glv1 = L.tf_glv(X)      # beta*X mod P
    glv2 = L.tf_glv2(X)     # beta^2*X mod P
    inv_X = L.tf_inv(X)
    inv_Y = L.tf_inv(Y)
    slope = L.tf_slope(X, Y) # Y/X mod P

    # === Second-order combos ===
    inv_X_plus_Y = L.tf_sum(inv_X, Y)
    glv1_times_Y = L.tf_prod(glv1, Y)

    # === Modular reductions ===
    selected_mods = [2, 3, 4, 5, 7, 8, 11, 13, 16, 17, 19, 23, 29, 31, 37, 43, 47, 53, 59, 61]

    for m in selected_mods:
        features[f'X%{m}'] = L.col_mod(X, m)
        features[f'Y%{m}'] = L.col_mod(Y, m)
        features[f'glv1%{m}'] = L.col_mod(glv1, m)
        features[f'glv2%{m}'] = L.col_mod(glv2, m)
        features[f'slope%{m}'] = L.col_mod(slope, m)
        features[f'inv_X+Y%{m}'] = L.col_mod(inv_X_plus_Y, m)
        features[f'glv1*Y%{m}'] = L.col_mod(glv1_times_Y, m)

    # === Legendre symbol ===
    selected_primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

    for p in selected_primes:
        features[f'leg_X_{p}'] = L.col_legendre(X, p)
        features[f'leg_Y_{p}'] = L.col_legendre(Y, p)
        features[f'leg_slope_{p}'] = L.col_legendre(slope, p)

    # === Bit patterns ===
    for b in range(16):
        features[f'X_bit{b}'] = L.col_bit(X, b)
        features[f'Y_bit{b}'] = L.col_bit(Y, b)
        features[f'slope_bit{b}'] = L.col_bit(slope, b)

    # === Hamming weight ===
    features['X_hamming'] = L.col_hamming(X)
    features['Y_hamming'] = L.col_hamming(Y)
    features['slope_hamming'] = L.col_hamming(slope)

    print(f"Built {len(features)} comprehensive features from curve transforms")
    return features

def build_positive_control(d):
    """Build control feature with ~0.3 bits of signal."""
    k = d['k']
    N = d['N']
    rng = np.random.default_rng(42)
    control = np.zeros(N, dtype=int)
    for i in range(N):
        if rng.random() < 0.7:
            control[i] = k[i] % 4
        else:
            control[i] = rng.integers(0, 4)
    return control

def run_hunt_v2(d):
    """Two-phase hunt with expanded feature set and top-500 filtering."""
    print(f"\n=== Curve-Transforms Leak Hunt V2 ===")
    print(f"Dataset: N={d['N']} keys")

    # === Build features and targets ===
    features = build_comprehensive_features(d)
    targets = L.build_target_set(d)

    # === Positive control ===
    control_feature = build_positive_control(d)
    targets['control_k%4'] = control_feature % 4
    features['CONTROL'] = control_feature

    # === Phase 1: Raw MI scan ===
    print(f"\nPhase 1: Raw MI scan for {len(features)} x {len(targets)} pairs...")
    raw_results = []

    for fname, f in features.items():
        for tname, t in targets.items():
            raw, A, B = L.mi_bits(f, t)
            raw_results.append({
                'feature': fname,
                'target': tname,
                'raw_mi': raw,
                'A': A,
                'B': B,
            })

    raw_results.sort(key=lambda r: r['raw_mi'], reverse=True)

    print(f"Raw MI scan complete. Top 10 raw MI:")
    for r in raw_results[:10]:
        print(f"  raw_mi={r['raw_mi']:.5f}: {r['feature']} -> {r['target']}")

    # === Phase 2: Adjusted MI on top 500 ===
    print(f"\nPhase 2: Computing adjusted MI (iters=5) for top 500...")
    top_500 = raw_results[:500]
    results = []

    for r in top_500:
        fname, tname = r['feature'], r['target']
        f, t = features[fname], targets[tname]
        adj_mi, raw, null_mean, A, B = L.adj_mi(f, t, iters=5)
        p = L.gtest_p(raw, d['N'], A, B)
        results.append({
            'feature': fname,
            'target': tname,
            'adj_mi': adj_mi,
            'raw_mi': raw,
            'null_mean': null_mean,
            'A': A,
            'B': B,
            'gtest_p': p,
        })

    results.sort(key=lambda r: r['adj_mi'], reverse=True)

    # === Report top 50 ===
    print(f"\n=== TOP 50 by Adjusted MI (of {len(results)} filtered) ===")
    print(f"{'Adj MI(b)':>10} {'Raw MI(b)':>10} {'Null(b)':>10} {'Gtest-p':>10} {'Bonf-p':>10}  feature -> target")
    print("-" * 100)

    M_total = len(raw_results)  # Conservative Bonferroni multiplier
    for i, r in enumerate(results[:50]):
        bonf_p = min(1.0, r['gtest_p'] * M_total)
        survived = "***" if (r['adj_mi'] > 0 and bonf_p < 0.01) else ""
        is_control = " [CONTROL]" if r['feature'] == 'CONTROL' else ""
        print(f"{r['adj_mi']:10.5f} {r['raw_mi']:10.5f} {r['null_mean']:10.5f} "
              f"{r['gtest_p']:10.2e} {bonf_p:10.2e}  {r['feature']} -> {r['target']} {survived}{is_control}")

    # === Filter out control and analyze real candidates ===
    real_results = [r for r in results if r['feature'] != 'CONTROL']

    print(f"\n=== ANALYSIS OF REAL CANDIDATES (excluding CONTROL) ===")
    print(f"Top 30 real candidates (by adj_mi):")
    print(f"{'Adj MI(b)':>10} {'Raw MI(b)':>10} {'Null(b)':>10} {'Gtest-p':>10} {'Bonf-p':>10}  feature -> target")
    print("-" * 100)

    for i, r in enumerate(real_results[:30]):
        bonf_p = min(1.0, r['gtest_p'] * M_total)
        survived = "***" if (r['adj_mi'] > 0.001 and bonf_p < 0.01) else ""
        print(f"{r['adj_mi']:10.5f} {r['raw_mi']:10.5f} {r['null_mean']:10.5f} "
              f"{r['gtest_p']:10.2e} {bonf_p:10.2e}  {r['feature']} -> {r['target']} {survived}")

    # === Survivors (strict) ===
    survivors_strict = [r for r in real_results if r['adj_mi'] > 0 and min(1.0, r['gtest_p'] * M_total) < 0.01]

    # === Survivors (relaxed) ===
    survivors_relaxed = [r for r in real_results if r['adj_mi'] > 0.001]

    print(f"\n=== SURVIVORS (STRICT: adj_mi > 0 AND Bonf-p < 0.01) ===")
    if survivors_strict:
        print(f"Found {len(survivors_strict)} candidates:")
        for r in survivors_strict[:15]:
            bonf_p = min(1.0, r['gtest_p'] * M_total)
            print(f"  adj_mi={r['adj_mi']:.5f}, raw_mi={r['raw_mi']:.5f}, bonf_p={bonf_p:.2e}")
            print(f"    -> {r['feature']} -> {r['target']}")
    else:
        print("None")

    print(f"\n=== CANDIDATES WORTH INVESTIGATING (adj_mi > 0.001) ===")
    if survivors_relaxed:
        print(f"Found {len(survivors_relaxed)} candidates:")
        for r in survivors_relaxed[:20]:
            bonf_p = min(1.0, r['gtest_p'] * M_total)
            print(f"  adj_mi={r['adj_mi']:.5f}, raw_mi={r['raw_mi']:.5f}, bonf_p={bonf_p:.2e}")
            print(f"    -> {r['feature']} -> {r['target']}")
    else:
        print("None with adj_mi > 0.001 (all candidates are noise)")

    # === Control check ===
    print(f"\n=== POSITIVE CONTROL CHECK ===")
    control_results = [r for r in results if r['feature'] == 'CONTROL']
    if control_results:
        cr = control_results[0]
        bonf_p = min(1.0, cr['gtest_p'] * M_total)
        print(f"CONTROL feature (70% k%4 + 30% noise):")
        print(f"  adj_mi={cr['adj_mi']:.5f} bits (expected ~0.2-0.3)")
        print(f"  raw_mi={cr['raw_mi']:.5f} bits")
        print(f"  Bonferroni-p={bonf_p:.2e}")
        if cr['adj_mi'] > 0.05:
            print(f"✓ CONTROL DETECTED")
        else:
            print(f"⚠ CONTROL WEAK (adj_mi = {cr['adj_mi']:.5f})")

    return results, survivors_strict, survivors_relaxed

if __name__ == '__main__':
    print("Loading dataset...")
    d = L.load()
    print(f"Loaded N={d['N']} keys")

    results, strict, relaxed = run_hunt_v2(d)

    print(f"\n=== FINAL SUMMARY ===")
    print(f"Pairs tested with adjusted MI: {len(results)}")
    print(f"Real candidates (strict): {len(strict)}")
    print(f"Real candidates (relaxed): {len(relaxed)}")
    if strict:
        print(f"Top (strict): {strict[0]['feature']} -> {strict[0]['target']}, adj_mi={strict[0]['adj_mi']:.5f}")
    if relaxed:
        print(f"Top (relaxed): {relaxed[0]['feature']} -> {relaxed[0]['target']}, adj_mi={relaxed[0]['adj_mi']:.5f}")
