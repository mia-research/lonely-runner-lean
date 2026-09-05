#!/usr/bin/env python3
"""
Curve-transforms leak hunt: Build features from curve-native transforms of (X,Y),
measure MI to targets, rank by adjusted MI, and verify with statistical tests.

GUARDRAIL: all features are ONLY functions of (X,Y) and curve constants.
Never read from n, k, or d.

OPTIMIZATION: Use raw MI first to filter down to top 100, then adjust MI on those.
"""
import sys
sys.path.insert(0, '/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/scripts/session_2026-07')

import leak_lib as L
import numpy as np

def build_curve_features_selective(d):
    """
    Build a reduced feature dict from curve transforms of (X,Y).
    Focus on the most likely candidates: modular reductions and Legendre symbols
    of core transforms (X, Y, slope, GLV images).
    """
    X, Y = d['X'], d['Y']
    N = d['N']
    features = {}

    # === Primary curve transforms ===
    glv1 = L.tf_glv(X)      # beta*X mod P
    slope = L.tf_slope(X, Y) # Y/X mod P

    # === Modular reductions: focus on small moduli (2, 3, 5, 7, 11, 13, etc.) ===
    selected_mods = [2, 3, 4, 5, 7, 8, 11, 13, 16, 17, 19, 23, 29, 31, 37, 43, 47]

    for m in selected_mods:
        features[f'X%{m}'] = L.col_mod(X, m)
        features[f'Y%{m}'] = L.col_mod(Y, m)
        features[f'glv1%{m}'] = L.col_mod(glv1, m)
        features[f'slope%{m}'] = L.col_mod(slope, m)

    # === Legendre symbol (quadratic residue) ===
    selected_primes = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]

    for p in selected_primes:
        features[f'leg_X_{p}'] = L.col_legendre(X, p)
        features[f'leg_Y_{p}'] = L.col_legendre(Y, p)
        features[f'leg_slope_{p}'] = L.col_legendre(slope, p)

    # === Bit patterns (low bits are most informative) ===
    for b in range(12):
        features[f'X_bit{b}'] = L.col_bit(X, b)
        features[f'Y_bit{b}'] = L.col_bit(Y, b)
        features[f'slope_bit{b}'] = L.col_bit(slope, b)

    # === Hamming weight ===
    features['X_hamming'] = L.col_hamming(X)
    features['Y_hamming'] = L.col_hamming(Y)
    features['slope_hamming'] = L.col_hamming(slope)

    print(f"Built {len(features)} features from curve transforms")
    return features

def build_positive_control(d):
    """
    Build a synthetic feature that genuinely carries ~0.3 bits about k%4.
    Method: 70% of the time, copy k%4; 30% of the time, random noise.
    """
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

def run_hunt(d):
    """Load data, build features, measure MI, report top candidates."""
    print(f"\n=== Curve-Transforms Leak Hunt (Optimized) ===")
    print(f"Dataset: N={d['N']} keys")
    print(f"Targets: n%m, k%m (m in [2..16]), nbit/kbit[0:8], kn_bucket16, n_bucket16")

    # === Build features (reduced set) ===
    features = build_curve_features_selective(d)

    # === Build targets ===
    targets = L.build_target_set(d)

    # === Positive control ===
    control_feature = build_positive_control(d)
    targets['control_k%4'] = control_feature % 4
    features['CONTROL'] = control_feature

    # === Phase 1: Raw MI scan to filter down ===
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

    # Sort by raw MI and keep top 200 for adjusted MI estimation
    raw_results.sort(key=lambda r: r['raw_mi'], reverse=True)
    top_200 = raw_results[:200]

    print(f"Phase 1 complete. Top 200 by raw MI identified.")
    print(f"Top 5 raw MI candidates:")
    for r in top_200[:5]:
        print(f"  raw_mi={r['raw_mi']:.5f}: {r['feature']} -> {r['target']}")

    # === Phase 2: Adjusted MI on top 200 ===
    print(f"\nPhase 2: Computing adjusted MI (raw - shuffle null, iters=5) for top 200...")
    results = []

    for r in top_200:
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

    # === Sort by adjusted MI ===
    results.sort(key=lambda r: r['adj_mi'], reverse=True)

    # === Report top 40 ===
    print(f"\n=== TOP 40 by Adjusted MI (of {len(results)} filtered pairs) ===")
    print(f"{'Adj MI(b)':>10} {'Raw MI(b)':>10} {'Null(b)':>10} {'Gtest-p':>10} {'Bonf-p':>10}  feature -> target")
    print("-" * 100)

    M = len(results)  # Bonferroni: multiply by 200 (the filtered set)
    M_total = len(raw_results)  # Full problem size for conservative Bonferroni

    for i, r in enumerate(results[:40]):
        bonf_p = min(1.0, r['gtest_p'] * M_total)
        survived = "***" if (r['adj_mi'] > 0 and bonf_p < 0.01) else ""
        print(f"{r['adj_mi']:10.5f} {r['raw_mi']:10.5f} {r['null_mean']:10.5f} "
              f"{r['gtest_p']:10.2e} {bonf_p:10.2e}  {r['feature']} -> {r['target']} {survived}")

    # === Identify survivors (adj_mi > 0 AND Bonferroni p < 0.01) ===
    print(f"\n=== SURVIVORS: adj_mi > 0 AND Bonferroni p < 0.01 ===")
    survivors = [r for r in results if r['adj_mi'] > 0 and min(1.0, r['gtest_p'] * M_total) < 0.01]

    if survivors:
        print(f"Found {len(survivors)} surviving candidates:")
        for r in survivors[:20]:
            bonf_p = min(1.0, r['gtest_p'] * M_total)
            print(f"  adj_mi={r['adj_mi']:.5f} bits, raw_mi={r['raw_mi']:.5f}, "
                  f"bonf_p={bonf_p:.2e}: {r['feature']} -> {r['target']}")
    else:
        print("No candidates survived threshold.")

    # === Control check ===
    print(f"\n=== POSITIVE CONTROL CHECK ===")
    control_results = [r for r in results if r['feature'] == 'CONTROL']
    if control_results:
        cr = control_results[0]
        bonf_p = min(1.0, cr['gtest_p'] * M_total)
        print(f"CONTROL feature (70% k%4, 30% noise):")
        print(f"  adj_mi={cr['adj_mi']:.5f} bits (expected ~0.2-0.3)")
        print(f"  raw_mi={cr['raw_mi']:.5f} bits")
        print(f"  null_mean={cr['null_mean']:.5f} bits (shuffle baseline)")
        print(f"  target={cr['target']}")
        print(f"  gtest_p={cr['gtest_p']:.2e}")
        print(f"  Bonferroni-p={bonf_p:.2e}")
        if cr['adj_mi'] > 0.05:
            print(f"✓ CONTROL DETECTED (adj_mi > 0.05 bits)")
        else:
            print(f"✗ CONTROL NOT DETECTED STRONGLY (adj_mi = {cr['adj_mi']:.5f})")
    else:
        print("Control feature not in top 200 raw MI.")

    return results, survivors

if __name__ == '__main__':
    print("Loading dataset...")
    d = L.load()
    print(f"Loaded N={d['N']} keys, bits range [{d['bits'].min()}, {d['bits'].max()}]")

    results, survivors = run_hunt(d)

    print(f"\n=== FINAL SUMMARY ===")
    print(f"Total (feature, target) pairs in full problem: {len(results) * (len(d['n']) // len(results)) if results else 'unknown'}")
    print(f"Pairs tested with adjusted MI: {len(results)}")
    print(f"Survivors (adj_mi > 0, Bonf-p < 0.01): {len(survivors)}")
    if survivors:
        top = survivors[0]
        print(f"Top candidate: {top['feature']} -> {top['target']}, "
              f"adj_mi={top['adj_mi']:.5f} bits, raw_mi={top['raw_mi']:.5f} bits")
