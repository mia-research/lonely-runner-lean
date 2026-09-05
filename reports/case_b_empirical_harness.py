#!/usr/bin/env python3
"""
Case B Empirical Harness v2 — Theorem 12.1 Case B (Fast Fibre Analysis)
=========================================================================
Instead of brute-force time scanning, analytically checks specific fibres:
  b* = (n-1)L/n   (late-window fibre)
  b2 = 2L/n       (second fibre)
  bk = kL/n  for k=1,...,n-1

For each fibre b = kL/n, computes:
  - T_rho = floor(rho * k / n)  for each non-divisible runner rho
  - T_div = floor(q_j * n * k / n) = q_j * k  for each divisible runner q_j*n
  - bad set from each runner
  - miss set = Z/nZ minus union of bad sets
  - Fibre is safe iff miss set non-empty AND all divisible runners have bad ≠ Z/nZ

Then for each (n, d1, d2, div_speeds), determines:
  - Which fibres are safe
  - The structural pattern of safe fibres
  - Whether b=2L/n or b=(n-1)L/n is always in the safe set

Goal: discover the minimal proof-friendly fibre family that always contains a safe fibre.
"""

from math import gcd
from collections import defaultdict
import json, sys

# ─── arithmetic helpers ───────────────────────────────────────────────────

def units_mod_n(n):
    return [r for r in range(1, n) if gcd(r, n) == 1]

def non_units_mod_n(n):
    return [r for r in range(1, n) if gcd(r, n) > 1]

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

def h_group(g, n):
    """H_g = {0, n/g, 2n/g, ...} (coset of multiples of n/g)."""
    step = n // g
    return set(range(0, n, step))

def bad_set(rho, T, n):
    """
    bad(rho, T, n) = residues r in Z/nZ s.t. rho*t is "bad" at floor T.
    - rho divisible (n | rho): Z/nZ if T ≡ 0 or n-1 (mod n), else empty.
    - rho unit (gcd=1):        {-T*rho^{-1}, -(T+1)*rho^{-1}} mod n
    - rho non-unit (gcd g):    H_g if g|T or g|(T+1), else empty.
    """
    g = gcd(rho, n)
    if g == n:
        # Divisible runner
        Tmod = T % n
        return set(range(n)) if (Tmod == 0 or Tmod == n - 1) else set()
    elif g == 1:
        # Unit runner
        inv = pow(rho, -1, n)
        return {(-T * inv) % n, (-(T + 1) * inv) % n}
    else:
        # Non-unit runner
        if T % g == 0 or (T + 1) % g == 0:
            return h_group(g, n)
        return set()

# ─── fibre analysis ────────────────────────────────────────────────────────

def analyse_fibre(n, k, retained_rho, div_qs, dropped_pair):
    """
    Analyse fibre b = k*L/n.

    At this fibre:
      T_rho = floor(rho * k / n)  for non-divisible runner rho
      T_div = q_j * k             for divisible runner q_j*n

    Returns dict with:
      miss_set, safe (bool), div_blocked (list of which div runners block)
    """
    coverage = set()
    div_blocked = []

    # Non-divisible runners
    for rho in retained_rho:
        T = (rho * k) // n
        bs = bad_set(rho, T, n)
        coverage |= bs

    # Divisible runners
    for q_j in div_qs:
        T = q_j * k   # floor(q_j * n * k / n) = q_j * k
        bs = bad_set(q_j * n, T, n)
        if len(bs) == n:   # full cover
            div_blocked.append(q_j)
            coverage = set(range(n))
        else:
            coverage |= bs

    miss = set(range(n)) - coverage
    safe = len(miss) > 0 and len(div_blocked) == 0

    return {
        'k': k,
        'miss': sorted(miss),
        'safe': safe,
        'div_blocked': div_blocked,
        'coverage_size': len(coverage),
    }

def analyse_tuple(n, d1, d2, div_qs):
    """
    Full fibre analysis for one (n, d1, d2, div_qs) configuration.
    """
    retained = [r for r in range(1, n) if r not in (d1, d2)]
    non_div = retained  # all with q=0 in Case B

    results = {}
    safe_ks = []

    for k in range(1, n):   # k = 1,...,n-1 correspond to fibres L/n,...,(n-1)L/n
        res = analyse_fibre(n, k, non_div, div_qs, (d1, d2))
        results[k] = res
        if res['safe']:
            safe_ks.append(k)

    return {
        'n': n, 'd1': d1, 'd2': d2, 'div_qs': div_qs,
        'safe_ks': safe_ks,
        'lrc_holds': len(safe_ks) > 0,
        'b2_safe': results.get(2, {}).get('safe', False),
        'bstar_safe': results.get(n - 1, {}).get('safe', False),
        'b1_safe': results.get(1, {}).get('safe', False),
        'min_safe_k': min(safe_ks) if safe_ks else None,
        'b2_miss': results.get(2, {}).get('miss', []),
        'bstar_miss': results.get(n - 1, {}).get('miss', []),
        'fibre_detail': {k: results[k] for k in [1, 2, n - 2, n - 1]},
    }

# ─── adversarial q configurations ─────────────────────────────────────────

def adversarial_div_configs(n, d1, d2):
    """
    Generate a representative set of |E_div|=2 divisible runner configurations.
    Covers: small q, CRT-adversarial q, large q.
    """
    configs = [
        ('q=1,2',    [1, 2]),
        ('q=1,3',    [1, 3]),
        ('q=2,3',    [2, 3]),
        ('q=1,n+1',  [1, n + 1]),
        ('q=7,11',   [7, 11]),
        ('q=1,79',   [1, 79]),
        ('q=79,131', [79, 131]),
        ('q=1,257',  [1, 257]),
    ]
    # CRT-adversarial: q ≡ 1 (mod n)  [worst case: q*k = k, divisible runner lands at (T ≡ k) mod n]
    crt_q = n + 1  # first q ≡ 1 mod n
    configs.append((f'q=1,{crt_q}(≡1modn)', [1, crt_q]))
    # q ≡ n-1 mod n: T = q_j*k ≡ (n-1)*k, could force T ≡ n-1 mod n when k=1
    configs.append((f'q=1,{n-1}', [1, n - 1]))
    configs.append((f'q=n-1,n+1', [n - 1, n + 1]))
    # Very large q
    configs.append(('q=1000,1001', [1000, 1001]))
    return configs

# ─── main sweep ─────────────────────────────────────────────────────────

def run_n_analysis(n, verbose=True):
    """Full analysis for n: all dropped pairs, all div configs."""
    pf = prime_factors(n)
    if verbose:
        print(f"\n{'='*60}")
        print(f"n = {n}   prime factors: {pf}")
        print(f"{'='*60}")

    non_units = non_units_mod_n(n)
    from itertools import combinations
    dropped_pairs = list(combinations(non_units, 2))

    all_results = []
    failures = []

    for d1, d2 in dropped_pairs:
        configs = adversarial_div_configs(n, d1, d2)
        pair_gcds = (gcd(d1, n), gcd(d2, n))

        for config_label, div_qs in configs:
            res = analyse_tuple(n, d1, d2, div_qs)
            res['config_label'] = config_label
            res['pair_gcds'] = pair_gcds
            all_results.append(res)

            if not res['lrc_holds']:
                failures.append(res)
                print(f"  *** FAIL: n={n}, d=({d1},{d2}), {config_label} ***")
            elif verbose and d1 == non_units[0] and d2 == non_units[1]:
                # Print first pair as sample
                b2s = '✓' if res['b2_safe'] else '✗'
                bss = '✓' if res['bstar_safe'] else '✗'
                print(f"  d=({d1},{d2}) gcd=({pair_gcds[0]},{pair_gcds[1]}) "
                      f"{config_label:20s}: "
                      f"safe_ks={res['safe_ks'][:5]}  "
                      f"b2={b2s} b*={bss}  "
                      f"min_safe_k={res['min_safe_k']}")

    if verbose:
        # Summary for this n
        b2_rate = sum(1 for r in all_results if r['b2_safe']) / len(all_results) * 100
        bstar_rate = sum(1 for r in all_results if r['bstar_safe']) / len(all_results) * 100
        print(f"\n  Summary n={n}: b=2L/n safe: {b2_rate:.1f}%  "
              f"b=b* safe: {bstar_rate:.1f}%  "
              f"LRC holds: {(1-len(failures)/len(all_results))*100:.1f}%")

    return all_results, failures


def summarise(all_results, all_failures):
    print(f"\n{'='*60}")
    print(f"GLOBAL SUMMARY")
    print(f"{'='*60}")
    print(f"Total configurations: {len(all_results)}")
    print(f"LRC failures:         {len(all_failures)}")

    if all_failures:
        for f in all_failures:
            print(f"  FAIL: n={f['n']}, d=({f['d1']},{f['d2']}), qs={f['div_qs']}")
    else:
        print("  LRC holds universally ✓")

    # b=2L/n universality
    b2_total = len(all_results)
    b2_hits = sum(1 for r in all_results if r['b2_safe'])
    bstar_hits = sum(1 for r in all_results if r['bstar_safe'])
    both_hits = sum(1 for r in all_results if r['b2_safe'] or r['bstar_safe'])
    print(f"\nFibre universality:")
    print(f"  b=2L/n safe:       {b2_hits:4d}/{b2_total} ({b2_hits/b2_total*100:.1f}%)")
    print(f"  b=(n-1)L/n safe:   {bstar_hits:4d}/{b2_total} ({bstar_hits/b2_total*100:.1f}%)")
    print(f"  b=2L/n OR b* safe: {both_hits:4d}/{b2_total} ({both_hits/b2_total*100:.1f}%)")

    # When b=2L/n fails: what k is the minimum safe k?
    b2_fails = [r for r in all_results if not r['b2_safe']]
    if b2_fails:
        print(f"\nWhen b=2L/n fails ({len(b2_fails)} configs):")
        min_ks = defaultdict(int)
        for r in b2_fails:
            mk = r['min_safe_k']
            min_ks[mk] += 1
        for mk, cnt in sorted(min_ks.items(), key=lambda x: (x[0] is None, x[0])):
            print(f"  min_safe_k={mk}: {cnt} configs")

    # Miss set at b=2L/n: what structure?
    print(f"\nMiss set at b=2L/n (when safe):")
    b2_miss_sizes = defaultdict(int)
    for r in all_results:
        if r['b2_safe']:
            b2_miss_sizes[len(r['b2_miss'])] += 1
    for size, cnt in sorted(b2_miss_sizes.items()):
        print(f"  |miss|={size}: {cnt} configs")

    # Miss set at b*: what structure?
    print(f"\nMiss set at b* (when safe):")
    bstar_miss_sizes = defaultdict(int)
    for r in all_results:
        if r['bstar_safe']:
            bstar_miss_sizes[len(r['bstar_miss'])] += 1
    for size, cnt in sorted(bstar_miss_sizes.items()):
        print(f"  |miss|={size}: {cnt} configs")

    # Divisibility pattern: which configs does b=2L/n fail for?
    print(f"\nb=2L/n failure pattern (by div_qs):")
    fail_by_qs = defaultdict(int)
    total_by_qs = defaultdict(int)
    for r in all_results:
        key = str(r['div_qs'])
        total_by_qs[key] += 1
        if not r['b2_safe']:
            fail_by_qs[key] += 1
    for key in sorted(fail_by_qs.keys(), key=lambda k: -fail_by_qs[k]):
        cnt = fail_by_qs[key]
        tot = total_by_qs[key]
        print(f"  qs={key:20s}: {cnt}/{tot} fail")


def main():
    n_values = [15, 21, 33, 35, 39, 45, 51]
    all_results, all_failures = [], []

    for n in n_values:
        res, fail = run_n_analysis(n, verbose=True)
        all_results.extend(res)
        all_failures.extend(fail)

    summarise(all_results, all_failures)

    # Save results
    outfile = "/Users/trentpalelei/Desktop/Math Ex/reports/case_b_harness_results.json"
    # Convert sets to lists for JSON
    for r in all_results:
        for key in ['b2_miss', 'bstar_miss', 'safe_ks']:
            if isinstance(r.get(key), set):
                r[key] = sorted(r[key])
        if 'fibre_detail' in r:
            for k, v in r['fibre_detail'].items():
                if isinstance(v.get('miss'), set):
                    v['miss'] = sorted(v['miss'])
    with open(outfile, 'w') as f:
        json.dump(all_results, f, indent=2)
    print(f"\nResults saved: {outfile}")

    return 0 if not all_failures else 1


if __name__ == '__main__':
    sys.exit(main())
