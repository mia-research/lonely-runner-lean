"""
Stratified (per-n, per-k) mutual information hunt for (X,Y) -> n/k leaks.

DESIGN:
1. (A) PER-N: for each n with >=300 keys, test whether (X,Y) features leak k
       within that group using adjusted MI (bias-corrected).
2. (B) PER-K: for each k with >=300 keys, test whether (X,Y) features leak n
       within that group.

FEATURES: functions of (X,Y) and curve constants ONLY. Never use n,k,d.
  - Residues mod small primes/powers
  - Legendre symbols
  - Slope Y/X
  - GLV transform (BETA*X mod P)
  - Bit operations

METRICS:
  - adjusted MI = raw MI - mean(shuffle MI) [bias correction]
  - For each group, compute many (feature, target) pairs
  - Count how many exceed the 99th percentile of shuffle baseline
  - Compare to expected-by-chance

GUARDRAILS:
  - Features NEVER use n, k, or d
  - Use adj_mi for bias correction (important for small alphabets)
  - POSITIVE CONTROL: plant a real feature and verify test catches it
  - Report actual numbers, never "closed" or "settled"
"""

import numpy as np
import leak_lib as L
import sys
from collections import defaultdict

def build_xy_features(d, mod_limit=61):
    """
    Build feature dict from (X,Y) and curve constants ONLY.
    Return dict name -> np.array of integers (small alphabet).
    """
    X, Y = d['X'], d['Y']
    feats = {}

    # Residues mod small numbers
    for m in L.SMALL_MODS:
        if m <= mod_limit:
            feats[f"X%{m}"] = L.col_mod(X, m)
            feats[f"Y%{m}"] = L.col_mod(Y, m)

    # Legendre symbols (quadratic residue)
    for p in L.SMALL_PRIMES:
        if p <= mod_limit:
            feats[f"X_leg{p}"] = L.col_legendre(X, p)
            feats[f"Y_leg{p}"] = L.col_legendre(Y, p)

    # Individual bits
    for b in range(0, 8):
        feats[f"X_bit{b}"] = L.col_bit(X, b)
        feats[f"Y_bit{b}"] = L.col_bit(Y, b)

    # Hamming weight
    feats["X_hamming"] = L.col_hamming(X)
    feats["Y_hamming"] = L.col_hamming(Y)

    # Slope Y/X (mod P)
    slope = L.tf_slope(X, Y)
    for m in [2, 3, 5, 7, 11, 13, 17, 19, 23]:
        feats[f"slope%{m}"] = L.col_mod(slope, m)

    # GLV transform (BETA*X mod P)
    glv = L.tf_glv(X)
    for m in [2, 3, 5, 7, 11, 13, 17, 19]:
        feats[f"GLV%{m}"] = L.col_mod(glv, m)

    # X*Y product
    prod = L.tf_prod(X, Y)
    for m in [2, 3, 5, 7, 11, 13]:
        feats[f"XY%{m}"] = L.col_mod(prod, m)

    # X+Y sum
    summ = L.tf_sum(X, Y)
    for m in [2, 3, 5, 7, 11]:
        feats[f"X+Y%{m}"] = L.col_mod(summ, m)

    return feats

def build_k_target(k_array, mod_limit=13):
    """Build target dict for k (what we're trying to predict)."""
    targets = {}
    for m in [2, 3, 4, 5, 6, 7, 8, 9, 11, 13]:
        if m <= mod_limit:
            targets[f"k%{m}"] = k_array % m
    for b in range(0, 8):
        targets[f"kbit{b}"] = (k_array >> b) & 1
    return targets

def build_n_target(n_array, mod_limit=13):
    """Build target dict for n (what we're trying to predict)."""
    targets = {}
    for m in [2, 3, 4, 5, 6, 7, 8, 9, 11, 13]:
        if m <= mod_limit:
            targets[f"n%{m}"] = n_array % m
    for b in range(0, 8):
        targets[f"nbit{b}"] = (n_array >> b) & 1
    return targets

def test_group(group_mask, xy_feats, target_dict, N_min=300, iters=8):
    """
    Test a single group (mask of rows) against target dict.
    Return list of (feature_name, target_name, adj_mi, raw_mi, shuffle_mi, A, B).
    """
    if group_mask.sum() < N_min:
        return []

    results = []
    group_size = group_mask.sum()
    rng = np.random.default_rng(42)  # Fixed seed for reproducibility

    for fname, feat_array in xy_feats.items():
        feat_group = feat_array[group_mask]
        for tname, targ_array in target_dict.items():
            targ_group = targ_array[group_mask]
            adj_mi, raw_mi, shuffle_mi, A, B = L.adj_mi(feat_group, targ_group, iters=iters, rng=rng)
            results.append((fname, tname, adj_mi, raw_mi, shuffle_mi, A, B, group_size))

    return results

def per_n_hunt(d, N_min=300, percentile=99):
    """
    (A) PER-N: for each n with >=N_min keys, find significant (feature, k) pairs.
    Return (n_vals_tested, sig_pairs, strongest_pair, shuffle_null_threshold).
    """
    print("\n" + "="*80)
    print("(A) PER-N HUNT: Does (X,Y) leak k within fixed n groups?")
    print("="*80)

    xy_feats = build_xy_features(d)
    n_array = d['n']
    k_array = d['k']
    k_targets = build_k_target(k_array)

    # Group by n
    n_unique = np.unique(n_array)
    n_groups = {}
    for nval in n_unique:
        mask = (n_array == nval)
        if mask.sum() >= N_min:
            n_groups[nval] = mask

    print(f"Found {len(n_groups)} distinct n values with >=N_min={N_min} keys:")
    print(f"  n values: {sorted(n_groups.keys())}")

    # Run tests
    all_results = []
    for nval in sorted(n_groups.keys()):
        mask = n_groups[nval]
        results = test_group(mask, xy_feats, k_targets, N_min=N_min, iters=8)
        for fname, tname, adj_mi, raw_mi, shuffle_mi, A, B, gsize in results:
            all_results.append({
                'n': nval,
                'feature': fname,
                'target': tname,
                'adj_mi': adj_mi,
                'raw_mi': raw_mi,
                'shuffle_mi': shuffle_mi,
                'A': A,
                'B': B,
                'group_size': gsize
            })

    # Compute null threshold (percentile of shuffle MI)
    shuffle_mis = [r['shuffle_mi'] for r in all_results]
    null_threshold = np.percentile(shuffle_mis, percentile)
    print(f"\nShuffle-MI {percentile}th percentile threshold: {null_threshold:.6f}")

    # Count significant (adj_mi > null threshold)
    sig_count = sum(1 for r in all_results if r['adj_mi'] > null_threshold)
    expected_sig = len(all_results) * (1 - percentile/100)

    print(f"Total (n, feature, target) triplets tested: {len(all_results)}")
    print(f"Significant (adj_mi > null threshold): {sig_count}")
    print(f"Expected by chance: {expected_sig:.1f}")
    print(f"Excess: {sig_count - expected_sig:.1f}")

    # Find strongest
    if all_results:
        strongest = max(all_results, key=lambda x: x['adj_mi'])
        print(f"\nStrongest per-n signal:")
        print(f"  n={strongest['n']}, feature={strongest['feature']}, target={strongest['target']}")
        print(f"  adjusted_mi={strongest['adj_mi']:.6f} bits")
        print(f"  raw_mi={strongest['raw_mi']:.6f}, shuffle_baseline={strongest['shuffle_mi']:.6f}")
        print(f"  alphabet: A={strongest['A']}, B={strongest['B']}, group_size={strongest['group_size']}")
        return len(n_groups), sig_count, strongest, null_threshold

    return len(n_groups), 0, None, null_threshold

def per_k_hunt(d, N_min=300, percentile=99):
    """
    (B) PER-K: for each k with >=N_min keys, find significant (feature, n) pairs.
    Return (k_vals_tested, sig_pairs, strongest_pair, shuffle_null_threshold).
    """
    print("\n" + "="*80)
    print("(B) PER-K HUNT: Does (X,Y) leak n within fixed k groups?")
    print("="*80)

    xy_feats = build_xy_features(d)
    n_array = d['n']
    k_array = d['k']
    n_targets = build_n_target(n_array)

    # Group by k
    k_unique = np.unique(k_array)
    k_groups = {}
    for kval in k_unique:
        mask = (k_array == kval)
        if mask.sum() >= N_min:
            k_groups[kval] = mask

    print(f"Found {len(k_groups)} distinct k values with >=N_min={N_min} keys:")
    print(f"  k values: {sorted(k_groups.keys())}")

    # Run tests
    all_results = []
    for kval in sorted(k_groups.keys()):
        mask = k_groups[kval]
        results = test_group(mask, xy_feats, n_targets, N_min=N_min, iters=8)
        for fname, tname, adj_mi, raw_mi, shuffle_mi, A, B, gsize in results:
            all_results.append({
                'k': kval,
                'feature': fname,
                'target': tname,
                'adj_mi': adj_mi,
                'raw_mi': raw_mi,
                'shuffle_mi': shuffle_mi,
                'A': A,
                'B': B,
                'group_size': gsize
            })

    # Compute null threshold
    shuffle_mis = [r['shuffle_mi'] for r in all_results]
    null_threshold = np.percentile(shuffle_mis, percentile)
    print(f"\nShuffle-MI {percentile}th percentile threshold: {null_threshold:.6f}")

    # Count significant
    sig_count = sum(1 for r in all_results if r['adj_mi'] > null_threshold)
    expected_sig = len(all_results) * (1 - percentile/100)

    print(f"Total (k, feature, target) triplets tested: {len(all_results)}")
    print(f"Significant (adj_mi > null threshold): {sig_count}")
    print(f"Expected by chance: {expected_sig:.1f}")
    print(f"Excess: {sig_count - expected_sig:.1f}")

    # Find strongest
    if all_results:
        strongest = max(all_results, key=lambda x: x['adj_mi'])
        print(f"\nStrongest per-k signal:")
        print(f"  k={strongest['k']}, feature={strongest['feature']}, target={strongest['target']}")
        print(f"  adjusted_mi={strongest['adj_mi']:.6f} bits")
        print(f"  raw_mi={strongest['raw_mi']:.6f}, shuffle_baseline={strongest['shuffle_mi']:.6f}")
        print(f"  alphabet: A={strongest['A']}, B={strongest['B']}, group_size={strongest['group_size']}")
        return len(k_groups), sig_count, strongest, null_threshold

    return len(k_groups), 0, None, null_threshold

def positive_control(d):
    """
    POSITIVE CONTROL: inject a real k-dependent feature into a subset
    and verify the test flags it.

    Strategy: for keys with n=1, artificially create a feature that
    correlates with k % 3. Then run the per-n hunt on just n=1 and
    verify it detects this planted feature.
    """
    print("\n" + "="*80)
    print("POSITIVE CONTROL: Plant a real k-dependent feature, verify detection")
    print("="*80)

    n_array = d['n']
    k_array = d['k']

    # Find all keys with n=1
    n1_mask = (n_array == 1)
    n1_count = n1_mask.sum()

    if n1_count < 300:
        print(f"Warning: only {n1_count} keys with n=1, skipping control (need >=300)")
        return None

    print(f"Found {n1_count} keys with n=1; will plant k%3 feature")

    # Plant the feature: k%3 for n=1 group
    k_planted = k_array % 3
    xy_feats_control = build_xy_features(d)
    xy_feats_control['PLANTED_k%3'] = k_planted  # Add planted feature

    k_targets = build_k_target(k_array)

    # Run test on n=1 group only
    results = test_group(n1_mask, xy_feats_control, k_targets, N_min=1, iters=8)

    # Find the planted feature result
    planted_results = [r for r in results if r[0] == 'PLANTED_k%3']

    if planted_results:
        for fname, tname, adj_mi, raw_mi, shuffle_mi, A, B, gsize in planted_results:
            if tname == 'k%3':
                print(f"\nPlanted feature k%3 result:")
                print(f"  Feature: {fname}")
                print(f"  Target: {tname}")
                print(f"  adjusted_mi: {adj_mi:.6f} bits")
                print(f"  raw_mi: {raw_mi:.6f}")
                print(f"  shuffle baseline: {shuffle_mi:.6f}")
                print(f"  group_size: {gsize}")

                # Compute what percentile this is among OTHER (feature, target) pairs
                other_adj_mis = [r[2] for r in results if r[0] != 'PLANTED_k%3']
                percentile_rank = 100 * sum(1 for x in other_adj_mis if x <= adj_mi) / len(other_adj_mis)
                print(f"  Percentile rank among other features: {percentile_rank:.1f}%")

                return {
                    'planted_adj_mi': adj_mi,
                    'planted_raw_mi': raw_mi,
                    'planted_shuffle_mi': shuffle_mi,
                    'percentile_rank': percentile_rank
                }

    return None

def main():
    print("Loading dataset...")
    d = L.load()
    print(f"Dataset: N={d['N']} keys")
    print(f"n range: {d['n'].min()}-{d['n'].max()}")
    print(f"k range: {d['k'].min()}-{d['k'].max()}")

    # (A) Per-n hunt
    n_tested, n_sig, n_strongest, n_null = per_n_hunt(d, N_min=300, percentile=99)

    # (B) Per-k hunt
    k_tested, k_sig, k_strongest, k_null = per_k_hunt(d, N_min=300, percentile=99)

    # Positive control
    ctrl = positive_control(d)

    # Summary
    print("\n" + "="*80)
    print("SUMMARY")
    print("="*80)
    print(f"\nPER-N RESULTS:")
    print(f"  N groups tested: {n_tested}")
    print(f"  Significant (feature, target) pairs: {n_sig}")
    print(f"  Null threshold (99th percentile shuffle MI): {n_null:.6f} bits")
    if n_strongest:
        print(f"  Strongest: n={n_strongest['n']}, {n_strongest['feature']} -> {n_strongest['target']}")
        print(f"             adj_mi = {n_strongest['adj_mi']:.6f} bits")

    print(f"\nPER-K RESULTS:")
    print(f"  K groups tested: {k_tested}")
    print(f"  Significant (feature, target) pairs: {k_sig}")
    print(f"  Null threshold (99th percentile shuffle MI): {k_null:.6f} bits")
    if k_strongest:
        print(f"  Strongest: k={k_strongest['k']}, {k_strongest['feature']} -> {k_strongest['target']}")
        print(f"             adj_mi = {k_strongest['adj_mi']:.6f} bits")

    print(f"\nPOSITIVE CONTROL:")
    if ctrl:
        print(f"  Planted k%3 feature (n=1 group):")
        print(f"    adjusted_mi: {ctrl['planted_adj_mi']:.6f} bits")
        print(f"    percentile rank: {ctrl['percentile_rank']:.1f}%")
    else:
        print(f"  Control not run (insufficient n=1 keys)")

    print(f"\n" + "="*80)

if __name__ == '__main__':
    main()
