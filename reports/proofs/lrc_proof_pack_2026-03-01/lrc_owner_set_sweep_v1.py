"""
lrc_owner_set_sweep_v1.py

Extended sweep: n=3..8, E_div={n}, all valid E_non tuples.
Records:
  - first-arrival runner at b_break (which runner completes coverage of witness r*)
  - gcd of first-arrival runner with n
  - ratio start_run / budget
  - palindrome symmetry verification

Also identifies worst-ratio tuples for Lemma BR.
"""

from math import gcd
from itertools import combinations


def safe_set(e, b, L, n):
    N = n * L
    result = set()
    for a in range(n):
        x = (e * (a * L + b)) % N
        if L <= x <= (n - 1) * L:
            result.add(a)
    return frozenset(result)


def A_b(e_non, b, L, n):
    if not e_non:
        return frozenset(range(n))
    result = safe_set(e_non[0], b, L, n)
    for e in e_non[1:]:
        result = result & safe_set(e, b, L, n)
    return result


def compute_b_div(n, L):
    return [b for b in range(L) if L <= n * b <= (n - 1) * L]


def lcm(a, b):
    return a * b // gcd(a, b)


def lcm_list(lst):
    r = 1
    for x in lst:
        r = lcm(r, x)
    return r


def analyze_fast(n, e_non, L):
    """Fast analysis without verbose output. Returns key metrics."""
    b_div = compute_b_div(n, L)
    if not b_div:
        return None
    b_lo, b_hi = b_div[0], b_div[-1]
    C_size = len(b_div)
    budget = (C_size - (n - 1)) / 2

    # Compute start_run and first good fiber
    start_run = 0
    b_break = None
    witness_r = None
    newly_arrived_runners = None

    for i, b in enumerate(b_div):
        ab = A_b(e_non, b, L, n)
        if ab:
            b_break = b
            witness_r = min(ab)  # take smallest witness residue
            # Find which runner newly arrived to complete coverage of witness_r
            if i > 0:
                b_prev = b_div[i - 1]
                owners_now = {e for e in e_non if witness_r in safe_set(e, b, L, n)}
                owners_prev = {e for e in e_non if witness_r in safe_set(e, b_prev, L, n)}
                newly_arrived_runners = owners_now - owners_prev
            else:
                newly_arrived_runners = set()
            break
        start_run += 1

    # end_run
    end_run = 0
    for b in reversed(b_div):
        ab = A_b(e_non, b, L, n)
        if not ab:
            end_run += 1
        else:
            break

    br_ok = start_run <= budget
    palindrome = (start_run == end_run)

    return {
        'n': n,
        'E_non': tuple(e_non),
        'L': L,
        'C_size': C_size,
        'start_run': start_run,
        'end_run': end_run,
        'b_break': b_break,
        'witness_r': witness_r,
        'newly_arrived': newly_arrived_runners,
        'newly_arrived_gcd': {gcd(e, n) for e in (newly_arrived_runners or set())},
        'budget': budget,
        'ratio': start_run / budget if budget > 0 else 0,
        'br_ok': br_ok,
        'palindrome': palindrome,
        'B_safe': C_size - 2 * start_run if palindrome else C_size - start_run - end_run,
    }


def sweep(n_range=range(3, 9), max_e_factor=3, max_per_n=2000):
    """Sweep and collect statistics."""
    all_results = []
    fails_br = []
    fails_pal = []

    for n in n_range:
        max_e = max_e_factor * n
        target_size = n - 2
        speeds = [e for e in range(1, max_e + 1) if e != n]
        count = 0
        n_results = []

        for combo in combinations(speeds, target_size):
            if count >= max_per_n:
                break
            e_all = list(combo) + [n]
            g = e_all[0]
            for x in e_all[1:]:
                g = gcd(g, x)
            if g != 1:
                continue
            L = lcm_list(e_all)

            r = analyze_fast(n, list(combo), L)
            if r is None:
                continue
            count += 1
            all_results.append(r)
            n_results.append(r)

            if not r['br_ok']:
                fails_br.append(r)
            if not r['palindrome']:
                fails_pal.append(r)

        # Per-n summary
        if n_results:
            max_ratio = max(r['ratio'] for r in n_results)
            avg_ratio = sum(r['ratio'] for r in n_results) / len(n_results)
            worst = max(n_results, key=lambda r: r['ratio'])
            # Newly-arrived runner gcd statistics
            gcd_hist = {}
            for r in n_results:
                for g in (r['newly_arrived_gcd'] or {0}):
                    gcd_hist[g] = gcd_hist.get(g, 0) + 1
            print(f"\nn={n}: {count} tuples, max_ratio={max_ratio:.4f}, avg_ratio={avg_ratio:.4f}")
            print(f"  Worst: E_non={worst['E_non']}, L={worst['L']}, "
                  f"start_run={worst['start_run']}, budget={worst['budget']:.1f}, "
                  f"ratio={worst['ratio']:.4f}")
            print(f"  Newly-arrived runner gcd distribution: {dict(sorted(gcd_hist.items()))}")

    print(f"\n{'='*64}")
    print(f"Total: {len(all_results)} tuples")
    print(f"Lemma BR failures:    {len(fails_br)}")
    print(f"Palindrome failures:  {len(fails_pal)}")

    if fails_br:
        print("\nLemma BR FAILURES:")
        for r in fails_br[:10]:
            print(f"  {r}")

    # Global worst-ratio tuples
    sorted_results = sorted(all_results, key=lambda r: -r['ratio'])
    print("\nTop 10 worst-ratio tuples:")
    for r in sorted_results[:10]:
        print(f"  n={r['n']}, E_non={r['E_non']}, L={r['L']}: "
              f"ratio={r['ratio']:.4f}, start_run={r['start_run']}, "
              f"budget={r['budget']:.1f}, "
              f"arrived_gcd={r['newly_arrived_gcd']}")

    # Check: is newly-arrived runner always gcd>1?
    unit_arrivals = [r for r in all_results
                     if r['start_run'] > 0 and 1 in (r['newly_arrived_gcd'] or set())]
    print(f"\nTuples with start_run>0 where a UNIT runner (gcd=1) newly arrives at b_break: {len(unit_arrivals)}")
    if unit_arrivals[:3]:
        for r in unit_arrivals[:3]:
            print(f"  n={r['n']}, E_non={r['E_non']}, arrived={r['newly_arrived']}, "
                  f"arrived_gcd={r['newly_arrived_gcd']}")

    return all_results, fails_br, fails_pal


if __name__ == '__main__':
    print("LRC Owner-Set Sweep v1 — Extended statistics")
    print("=" * 64)
    results, fails_br, fails_pal = sweep(n_range=range(3, 9), max_e_factor=3, max_per_n=1000)
