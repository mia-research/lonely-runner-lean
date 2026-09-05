"""
lrc_lemma_br_last_runner_profile_v1.py

For each unit-runner tuple with A_{b_lo}=∅:
  1. Find all residues with exactly 1 exclusion (min-exclusion residues).
  2. For each such r, find the unique excluder e* and its zone.
  3. Report: is e* > n? What is arr/budget?
  4. Check: does e* > n ALWAYS hold for at least one optimal witness?
  5. What is the minimum e* over all 1-exclusion optimal witnesses?

Key structural question:
  - Can a small runner (e* ≤ n) be the unique excluder of the optimal witness?
  - If so, does it still satisfy arr ≤ budget?
"""

from math import gcd
from itertools import combinations
from functools import reduce


def modinv(a, m):
    g, x, _ = extended_gcd(a, m)
    return x % m


def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x


def safe_set(e, b, L, n):
    N = n * L
    result = set()
    for a in range(n):
        x = (e * (a * L + b)) % N
        if L <= x <= (n - 1) * L:
            result.add(a)
    return frozenset(result)


def arr_time(e, r, b_lo, L, n):
    N = n * L
    x0 = (e * (r * L + b_lo)) % N
    if L <= x0 <= (n - 1) * L:
        return 0
    gap = (L - x0) if x0 < L else (N - x0 + L)
    assert gap % e == 0
    return gap // e


def x_val(e, r, b_lo, L, n):
    return (e * (r * L + b_lo)) % (n * L)


def a_low_formula(e, n):
    """Lower-zone excluded residue: a_low = -q * s^{-1} mod n"""
    if gcd(e, n) != 1:
        return None
    s = e % n
    q = e // n
    if s == 0:
        return None
    return (-q * modinv(s, n)) % n


def a_high_formula(e, n):
    """Upper-zone excluded residue: a_high = -s^{-1}*(1+q) mod n"""
    if gcd(e, n) != 1:
        return None
    s = e % n
    q = e // n
    if s == 0:
        return None
    return (-modinv(s, n) * (1 + q)) % n


def profile_unit_tuples(n_range=range(3, 10), max_e_factor=5, max_per_n=500):
    """
    For each unit-runner tuple with A_{b_lo}=∅:
    - Find 1-exclusion residues and their unique excluders
    - Profile: is e* > n? what zone? what is arr/budget?
    """
    def lcm(a, b): return a * b // gcd(a, b)
    def lcm_list(lst):
        r = 1
        for x in lst:
            r = lcm(r, x)
        return r

    print("=" * 70)
    print("Last-runner profile for unit-runner tuples")
    print("=" * 70)

    total = 0
    e_star_leq_n = 0   # cases where optimal e* ≤ n
    e_star_gt_n = 0    # cases where optimal e* > n
    always_gt_n = 0    # cases where ALL 1-exclusion witnesses have e* > n
    has_leq_n_with_ok = 0   # e* ≤ n but arr ≤ budget
    has_leq_n_with_fail = 0  # e* ≤ n and arr > budget (must be rescued by other witness)

    # Track e* values and their zones
    e_star_profile = {}  # e* -> count of times it's the optimal unique excluder
    min_e_star_seen = float('inf')

    for n in n_range:
        max_e = max_e_factor * n
        unit_speeds = [e for e in range(1, max_e + 1) if gcd(e, n) == 1 and e != n]
        count = 0
        n_fail = 0

        for combo in combinations(unit_speeds, n - 2):
            if count >= max_per_n:
                break
            e_all = list(combo) + [n]
            g = e_all[0]
            for x in e_all[1:]:
                g = gcd(g, x)
            if g != 1:
                continue
            L = lcm_list(e_all)
            b_lo = L // n
            budget = (n - 2) * (L - n) / (2 * n)
            if budget <= 0:
                count += 1
                continue

            # Check A_{b_lo} = empty
            safe_sets = {e: safe_set(e, b_lo, L, n) for e in combo}
            Ab = reduce(lambda x, y: x & y, [safe_sets[e] for e in combo])
            count += 1
            if Ab:
                continue  # Case A (trivial)

            total += 1
            N = n * L

            # Compute exclusions for each residue
            exclusions = {}
            for r in range(n):
                exc = []
                for e in combo:
                    if r not in safe_sets[e]:
                        x = x_val(e, r, b_lo, L, n)
                        zone = 'lower' if x < L else 'upper'
                        arr = arr_time(e, r, b_lo, L, n)
                        exc.append((e, zone, arr))
                exclusions[r] = exc

            min_exc = min(len(exclusions[r]) for r in range(n))

            # Find 1-exclusion residues
            one_exc_residues = [(r, exclusions[r][0]) for r in range(n)
                                if len(exclusions[r]) == min_exc == 1]

            if not one_exc_residues:
                # min_exc > 1 (multiple excluders for all residues)
                # Find optimal r* anyway
                all_recs = []
                for r in range(n):
                    exc = exclusions[r]
                    if exc:
                        max_arr = max(a for _, _, a in exc)
                        all_recs.append((max_arr, r, exc))
                all_recs.sort()
                best_arr, best_r, best_exc = all_recs[0]
                ok = best_arr <= budget
                if not ok:
                    n_fail += 1
                continue

            # Among 1-exclusion residues, find optimal (min arr)
            best_arr = float('inf')
            best_r = None
            best_e = None
            best_zone = None

            for r, (e, zone, arr) in one_exc_residues:
                if arr < best_arr:
                    best_arr = arr
                    best_r = r
                    best_e = e
                    best_zone = zone

            ok = best_arr <= budget

            if not ok:
                n_fail += 1
                print(f"  FAIL: n={n}, combo={combo}, L={L}, "
                      f"r*={best_r}, e*={best_e}(>n?{best_e>n}), zone={best_zone}, "
                      f"arr={best_arr:.2f}, budget={budget:.2f}")

            # Profile e*
            if best_e > n:
                e_star_gt_n += 1
            else:
                e_star_leq_n += 1
                if ok:
                    has_leq_n_with_ok += 1
                else:
                    has_leq_n_with_fail += 1

            e_star_profile[best_e] = e_star_profile.get(best_e, 0) + 1
            min_e_star_seen = min(min_e_star_seen, best_e)

            # Check if ALL 1-exclusion residues have e* > n
            if all(e > n for r, (e, zone, arr) in one_exc_residues):
                always_gt_n += 1

        if count > 0:
            print(f"n={n}: checked {count} combos, {total} with A_b_lo=∅, {n_fail} failures")

    print(f"\n{'='*70}")
    print("Summary:")
    print(f"  Total tuples with A_b_lo=∅: {total}")
    print(f"  e* > n: {e_star_gt_n} ({100*e_star_gt_n/total:.1f}%)")
    print(f"  e* ≤ n: {e_star_leq_n} ({100*e_star_leq_n/total:.1f}%)")
    print(f"    - e* ≤ n and arr ≤ budget: {has_leq_n_with_ok}")
    print(f"    - e* ≤ n and arr > budget: {has_leq_n_with_fail}")
    print(f"  All 1-exc witnesses have e* > n: {always_gt_n} ({100*always_gt_n/total:.1f}%)")
    print(f"  Minimum e* seen: {min_e_star_seen}")
    print(f"\n  e* frequency (top 15):")
    for e, cnt in sorted(e_star_profile.items(), key=lambda x: -x[1])[:15]:
        print(f"    e*={e}: {cnt} times")


def verify_large_runner_lower_zone_bound(n_range=range(3, 12)):
    """
    Verify: for e* > n (i.e., q* ≥ 1) and r* = a_low(e*):
      arr(e*, r*) = L(n-s*)/(n*e*) ≤ budget = (n-2)(L-n)/(2n)
    iff 2(n-s*)*L ≤ (n-2)*(L-n)*e*
    For e* ≥ n+1: check this algebraically.
    """
    print(f"\n{'='*70}")
    print("Algebraic bound: arr_lower ≤ budget for e* ≥ n+1")
    fails = 0

    for n in n_range:
        for e_star in range(n + 1, 6 * n + 1):
            if gcd(e_star, n) != 1:
                continue
            s = e_star % n  # s ∈ {1,...,n-1}
            q = e_star // n  # q ≥ 1

            # Check for multiple L values (L must be a multiple of n and e*)
            # Simplest L = lcm(e*, n) = e* * n (since gcd(e*,n)=1)
            L = e_star * n
            budget = (n - 2) * (L - n) / (2 * n)
            arr_low = L * (n - s) / (n * e_star)

            if arr_low > budget + 1e-9:
                fails += 1
                if fails <= 5:
                    print(f"  FAIL: n={n}, e*={e_star}, s={s}, q={q}, L={L}: "
                          f"arr={arr_low:.4f}, budget={budget:.4f}")

            # Also check L = 2*e*n, 3*e*n (larger L)
            for k in range(2, 5):
                L2 = k * e_star * n
                budget2 = (n - 2) * (L2 - n) / (2 * n)
                arr_low2 = L2 * (n - s) / (n * e_star)
                if arr_low2 > budget2 + 1e-9:
                    fails += 1
                    if fails <= 5:
                        print(f"  FAIL (k={k}): n={n}, e*={e_star}, s={s}, L={L2}: "
                              f"arr={arr_low2:.4f}, budget={budget2:.4f}")

    if fails == 0:
        print("  ✓ arr_lower ≤ budget for all e* ≥ n+1, all tested L.")
    else:
        print(f"  FAIL count: {fails}")


def prove_A_blo_requires_large_runner(n_range=range(3, 10), max_e_factor=5, max_per_n=500):
    """
    Verify: if all runners in E_non have e < n, then A_{b_lo} ≠ ∅.
    (I.e., Case B requires at least one runner > n.)
    """
    def lcm(a, b): return a * b // gcd(a, b)
    def lcm_list(lst):
        r = 1
        for x in lst:
            r = lcm(r, x)
        return r

    print(f"\n{'='*70}")
    print("Verify: A_b_lo=∅ requires ∃ e > n in E_non (for unit runners)")

    all_small_with_empty = 0  # tuples where all e < n BUT A_b_lo=∅ (should be 0)
    checked = 0

    for n in n_range:
        # Only test combos with all e < n
        small_speeds = [e for e in range(1, n) if gcd(e, n) == 1]
        if len(small_speeds) < n - 2:
            continue
        count = 0
        for combo in combinations(small_speeds, n - 2):
            if count >= max_per_n:
                break
            e_all = list(combo) + [n]
            g = e_all[0]
            for x in e_all[1:]:
                g = gcd(g, x)
            if g != 1:
                continue
            L = lcm_list(e_all)
            b_lo = L // n
            safe_sets = {e: safe_set(e, b_lo, L, n) for e in combo}
            Ab = reduce(lambda x, y: x & y, [safe_sets[e] for e in combo])
            checked += 1
            count += 1
            if not Ab:
                all_small_with_empty += 1
                print(f"  COUNTEREXAMPLE: n={n}, E_non={combo}, A_b_lo=∅!")

    print(f"  Checked {checked} all-small-runner tuples.")
    if all_small_with_empty == 0:
        print(f"  ✓ All had A_b_lo ≠ ∅. Case B always requires e > n in E_non.")
    else:
        print(f"  FAIL: {all_small_with_empty} tuples had all e < n but A_b_lo=∅.")


def analyze_small_e_witnesses(n_range=range(3, 9), max_e_factor=5, max_per_n=300):
    """
    Deep dive: when e* ≤ n is the unique excluder of the optimal witness:
    - Why does arr ≤ budget still hold?
    - What structural property ensures this?
    """
    def lcm(a, b): return a * b // gcd(a, b)
    def lcm_list(lst):
        r = 1
        for x in lst:
            r = lcm(r, x)
        return r

    print(f"\n{'='*70}")
    print("Analysis of small-e* witnesses (e* ≤ n)")

    cases = []

    for n in n_range:
        max_e = max_e_factor * n
        unit_speeds = [e for e in range(1, max_e + 1) if gcd(e, n) == 1 and e != n]
        count = 0

        for combo in combinations(unit_speeds, n - 2):
            if count >= max_per_n:
                break
            e_all = list(combo) + [n]
            g = e_all[0]
            for x in e_all[1:]:
                g = gcd(g, x)
            if g != 1:
                continue
            L = lcm_list(e_all)
            b_lo = L // n
            budget = (n - 2) * (L - n) / (2 * n)
            if budget <= 0:
                count += 1
                continue

            safe_sets = {e: safe_set(e, b_lo, L, n) for e in combo}
            Ab = reduce(lambda x, y: x & y, [safe_sets[e] for e in combo])
            count += 1
            if Ab:
                continue

            # Find 1-exclusion residues with e* ≤ n
            for r in range(n):
                exc = [(e, 'lower' if (e*(r*L+b_lo))%(n*L) < L else 'upper',
                        arr_time(e, r, b_lo, L, n))
                       for e in combo if r not in safe_sets[e]]
                if len(exc) == 1:
                    e_star, zone, arr = exc[0]
                    if e_star <= n:
                        cases.append({
                            'n': n, 'combo': combo, 'L': L,
                            'r': r, 'e_star': e_star, 'zone': zone,
                            'arr': arr, 'budget': budget,
                            'ok': arr <= budget,
                            'ratio': arr / budget if budget > 0 else 0
                        })

    print(f"  Total small-e* unique-exclusion cases: {len(cases)}")
    fails = [c for c in cases if not c['ok']]
    print(f"  Failures (arr > budget): {len(fails)}")

    if cases:
        print(f"\n  Zone distribution:")
        lower = sum(1 for c in cases if c['zone'] == 'lower')
        upper = sum(1 for c in cases if c['zone'] == 'upper')
        print(f"    Lower: {lower}, Upper: {upper}")

        print(f"\n  Max ratio (arr/budget): {max(c['ratio'] for c in cases):.4f}")
        print(f"  E* values seen (≤ n): {sorted(set(c['e_star'] for c in cases))}")

        # Show worst cases
        worst = sorted(cases, key=lambda c: -c['ratio'])[:5]
        print(f"\n  Worst ratio cases:")
        for c in worst:
            print(f"    n={c['n']}, E_non={c['combo']}, L={c['L']}: "
                  f"r*={c['r']}, e*={c['e_star']}(≤n), zone={c['zone']}, "
                  f"arr={c['arr']:.2f}, budget={c['budget']:.2f}, ratio={c['ratio']:.4f}")


if __name__ == '__main__':
    # 1. Algebraic bound for large runners in lower zone
    verify_large_runner_lower_zone_bound(n_range=range(3, 12))

    # 2. Verify A_b_lo=∅ requires a runner > n
    prove_A_blo_requires_large_runner(n_range=range(3, 9), max_per_n=500)

    # 3. Profile the optimal witness's unique excluder e*
    profile_unit_tuples(n_range=range(3, 9), max_e_factor=5, max_per_n=400)

    # 4. Deep dive on small-e* witnesses
    analyze_small_e_witnesses(n_range=range(3, 9), max_e_factor=5, max_per_n=300)
