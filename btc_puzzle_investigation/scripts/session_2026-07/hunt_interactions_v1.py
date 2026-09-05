#!/usr/bin/env python3
"""
Interaction hunt: Test higher-order products and ratios of transforms.
E.g., (X%p) * (Y%q), (X%p) + (slope%q), etc.
This is a guard against missing multi-feature leaks.
"""
import sys
sys.path.insert(0, '/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/scripts/session_2026-07')

import leak_lib as L
import numpy as np

def build_interaction_features(d):
    """
    Build pairwise product features from primary modular reductions.
    Focus on small moduli to keep alphabet size tractable.
    """
    X, Y = d['X'], d['Y']
    N = d['N']
    features = {}

    # === Base features ===
    glv1 = L.tf_glv(X)
    slope = L.tf_slope(X, Y)

    # === Small moduli for tractable interactions ===
    small_mods = [2, 3, 4, 5, 7, 11, 13]

    # Reduce to small moduli
    X_mod = {m: L.col_mod(X, m) for m in small_mods}
    Y_mod = {m: L.col_mod(Y, m) for m in small_mods}
    glv_mod = {m: L.col_mod(glv1, m) for m in small_mods}
    slope_mod = {m: L.col_mod(slope, m) for m in small_mods}

    # === Pairwise products ===
    # Product of (X%m1) * (Y%m2) mod min(m1,m2)
    for m1 in small_mods:
        for m2 in small_mods:
            if m1 <= m2:
                prod = (X_mod[m1] * Y_mod[m2]) % min(m1, m2)
                features[f'(X%{m1})*(Y%{m2})%{min(m1,m2)}'] = prod

    # Product of (X%m) * (slope%m) mod m
    for m in small_mods:
        prod = (X_mod[m] * slope_mod[m]) % m
        features[f'(X*slope)%{m}'] = prod

    # Product of (Y%m) * (slope%m) mod m
    for m in small_mods:
        prod = (Y_mod[m] * slope_mod[m]) % m
        features[f'(Y*slope)%{m}'] = prod

    # === Pairwise sums ===
    for m in small_mods:
        s = (X_mod[m] + Y_mod[m]) % m
        features[f'(X+Y)%{m}'] = s
        s = (X_mod[m] + slope_mod[m]) % m
        features[f'(X+slope)%{m}'] = s
        s = (Y_mod[m] + slope_mod[m]) % m
        features[f'(Y+slope)%{m}'] = s

    # === XOR (mod 2 differences) ===
    for m in small_mods:
        if m >= 3:  # XOR makes sense for m > 2
            xor_xy = (X_mod[2] + Y_mod[2]) % 2
            features[f'(X xor Y)'] = xor_xy
            break

    print(f"Built {len(features)} interaction features")
    return features

def run_interaction_hunt(d):
    """Test interaction features for leakage."""
    print(f"\n=== Interaction Hunt V1 ===")
    print(f"Dataset: N={d['N']} keys")

    # === Build features ===
    features = build_interaction_features(d)

    # === Build targets ===
    targets = L.build_target_set(d)

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

    print(f"Raw MI scan complete. Top 10:")
    for r in raw_results[:10]:
        print(f"  raw_mi={r['raw_mi']:.5f}: {r['feature']} -> {r['target']}")

    # === Phase 2: Top 100 with adjusted MI ===
    print(f"\nPhase 2: Adjusted MI for top 100...")
    top_100 = raw_results[:100]
    results = []

    for r in top_100:
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

    # === Report ===
    print(f"\n=== TOP 30 by Adjusted MI ===")
    print(f"{'Adj MI(b)':>10} {'Raw MI(b)':>10} {'Null(b)':>10} {'Gtest-p':>10}  feature -> target")
    print("-" * 90)

    for r in results[:30]:
        print(f"{r['adj_mi']:10.5f} {r['raw_mi']:10.5f} {r['null_mean']:10.5f} "
              f"{r['gtest_p']:10.2e}  {r['feature']} -> {r['target']}")

    # === Any survivors? ===
    M_total = len(raw_results)
    survivors = [r for r in results if r['adj_mi'] > 0 and r['gtest_p'] * M_total < 0.01]

    print(f"\n=== SURVIVORS (adj_mi > 0, Bonf-p < 0.01) ===")
    if survivors:
        print(f"Found {len(survivors)}:")
        for r in survivors:
            print(f"  adj_mi={r['adj_mi']:.5f}: {r['feature']} -> {r['target']}")
    else:
        print("None")

    return results

if __name__ == '__main__':
    print("Loading dataset...")
    d = L.load()
    print(f"Loaded N={d['N']} keys")

    results = run_interaction_hunt(d)

    print(f"\n=== SUMMARY ===")
    print(f"Interaction features tested: {len(results)}")
    max_adj = max(r['adj_mi'] for r in results) if results else 0
    print(f"Max adjusted MI: {max_adj:.5f} bits")
