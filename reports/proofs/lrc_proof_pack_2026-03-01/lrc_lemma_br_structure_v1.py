"""
lrc_lemma_br_structure_v1.py

Investigates:
1. Pigeonhole: for unit-runner tuples, every residue excluded by ≤1 runner → find such r*
2. For each r*, verify max_e arr(e,r*) ≤ budget
3. Upper-excluded-residue formula: a_high(e) = -s^{-1}(1+q) mod n
4. Arrival formula for upper zone: arr = L*(2n-s)/(n*e*)
5. Key: does the pigeonhole r* (excluded by fewest runners) always achieve arr ≤ budget?
"""

from math import gcd
from itertools import combinations


def modinv(a, m):
    """Extended Euclidean inverse of a mod m (requires gcd(a,m)=1)."""
    g, x, _ = extended_gcd(a, m)
    assert g == 1
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
    """Arrival time: steps from b_lo until r ∈ safe_set(e, b_lo + arr)."""
    N = n * L
    x0 = (e * (r * L + b_lo)) % N
    if L <= x0 <= (n - 1) * L:
        return 0
    if x0 < L:
        gap = L - x0
    else:
        gap = N - x0 + L
    assert gap % e == 0, f"gap={gap} not divisible by e={e}"
    return gap // e


def upper_excluded_residue(e, n):
    """
    For unit runner e (gcd(e,n)=1), compute a_high = upper-zone excluded residue at b_lo.
    Formula: a_high = -s^{-1}*(1+q) mod n, where s=e%n, q=e//n.
    """
    assert gcd(e, n) == 1
    s = e % n
    q = e // n
    s_inv = modinv(s, n)
    return (-s_inv * (1 + q)) % n


def lower_excluded_residue(e, n):
    """
    For unit runner e, compute a_low = lower-zone excluded residue at b_lo.
    a_low = -s^{-1}*q mod n? Let's derive from x < L condition.
    x_{e,a}(b_lo) = (e*(a*L+L/n)) mod nL. For lower zone: x < L.
    x/L = (q + s*(a + 1/n)) mod n < 1.
    So (q + s*a + s/n) mod n < 1.
    Integer part: (q + s*a) mod n = 0 → s*a ≡ -q (mod n) → a = -q*s^{-1} mod n.
    """
    assert gcd(e, n) == 1
    s = e % n
    q = e // n
    s_inv = modinv(s, n)
    return (-q * s_inv) % n


def analyze_unit_pigeonhole(n, e_non, L):
    """
    For a unit-runner tuple, analyze the pigeonhole structure:
    - For each residue r, count how many runners exclude it
    - Find r* with fewest exclusions
    - Compute max_e arr(e, r*) and compare to budget
    """
    b_lo = L // n
    budget = (n - 2) * (L - n) / (2 * n)

    # Compute safe sets at b_lo
    safe_sets = {e: safe_set(e, b_lo, L, n) for e in e_non}

    # Count exclusions per residue
    exclusions = {}  # r -> list of (e, zone, arr)
    for r in range(n):
        exc = []
        for e in e_non:
            if r not in safe_sets[e]:
                x0 = (e * (r * L + b_lo)) % (n * L)
                zone = 'lower' if x0 < L else 'upper'
                arr = arr_time(e, r, b_lo, L, n)
                exc.append((e, zone, arr))
        exclusions[r] = exc

    # Find r* with fewest exclusions
    min_exc = min(len(exclusions[r]) for r in range(n))
    best_residues = [r for r in range(n) if len(exclusions[r]) == min_exc]

    # Among best, find r* with minimum max_arr
    def max_arr_for_r(r):
        if not exclusions[r]:
            return 0
        return max(arr for _, _, arr in exclusions[r])

    r_star = min(best_residues, key=max_arr_for_r)
    max_arr = max_arr_for_r(r_star)

    return {
        'r_star': r_star,
        'min_exclusions': min_exc,
        'max_arr': max_arr,
        'budget': budget,
        'ratio': max_arr / budget if budget > 0 else 0,
        'ok': max_arr <= budget,
        'exclusions': exclusions,
    }


def sweep_unit_tuples(n_range=range(3, 9), max_e_factor=4, max_per_n=500):
    """Sweep over unit-runner tuples (all gcd(e,n)=1), check pigeonhole bound."""

    def lcm(a, b): return a * b // gcd(a, b)

    def lcm_list(lst):
        r = 1
        for x in lst:
            r = lcm(r, x)
        return r

    results = []
    fails = []

    for n in n_range:
        # For prime n: all non-n speeds have gcd=1
        if not all(p > 1 for p in [2, 3, 5, 7, 11, 13] if n % p == 0 and p != n):
            # not necessarily prime; just test all
            pass
        max_e = max_e_factor * n
        target_size = n - 2
        # Unit speeds: gcd(e,n)=1 and e != n
        unit_speeds = [e for e in range(1, max_e + 1) if gcd(e, n) == 1 and e != n]

        count = 0
        for combo in combinations(unit_speeds, target_size):
            if count >= max_per_n:
                break
            e_all = list(combo) + [n]
            g = e_all[0]
            for x in e_all[1:]:
                g = gcd(g, x)
            if g != 1:
                continue
            L = lcm_list(e_all)

            b_div = [b for b in range(L) if L <= n * b <= (n - 1) * L]
            if not b_div:
                continue

            b_lo = L // n
            budget = (n - 2) * (L - n) / (2 * n)

            # Check if A_{b_lo} = emptyset (start_run > 0 required for interesting cases)
            from functools import reduce
            def A_b_val(b):
                sets = [safe_set(e, b, L, n) for e in combo]
                return reduce(lambda x, y: x & y, sets)

            if A_b_val(b_lo):
                # start_run = 0, boring
                count += 1
                continue

            # Interesting case: A_{b_lo} = emptyset
            r = analyze_unit_pigeonhole(n, list(combo), L)
            r['n'] = n
            r['E_non'] = combo
            r['L'] = L
            count += 1
            results.append(r)
            if not r['ok']:
                fails.append(r)

    print(f"\nUnit-runner sweep ({n_range}): {len(results)} tuples with start_run>0")
    print(f"Pigeonhole bound failures: {len(fails)}")

    # Summary by n
    for n in n_range:
        n_res = [r for r in results if r['n'] == n]
        if n_res:
            max_ratio = max(r['ratio'] for r in n_res)
            max_exc = max(r['min_exclusions'] for r in n_res)
            print(f"  n={n}: {len(n_res)} tuples, max_ratio={max_ratio:.4f}, max_min_exclusions={max_exc}")

    if fails:
        print("\nFAILURES:")
        for r in fails[:5]:
            print(f"  n={r['n']}, E_non={r['E_non']}, r*={r['r_star']}, max_arr={r['max_arr']}, budget={r['budget']:.2f}")

    return results, fails


def check_formula_verification(n_range=range(4, 9), max_e=30):
    """
    Verify: for unit runner e, a_high = -s^{-1}*(1+q) mod n.
    Verify: arr(e, a_high) = L*(2n-s)/(n*e) for specific L.
    """
    print(f"\n{'='*60}")
    print("Verifying upper-excluded-residue formula")
    fails = 0
    checks = 0

    for n in n_range:
        L = 1  # use L=n (canonical, but b_lo=1) — actually needs L divisible by n
        # Use L = n * (something). For formula check, just need L=n*K for integer K.
        # Use L = lcm(n, e) for simplicity.
        for e in range(1, max_e + 1):
            if gcd(e, n) != 1:
                continue
            if e == n:
                continue
            L = e * n  # simplest L divisible by both n and e
            b_lo = L // n  # = e
            N = n * L

            # Compute safe_set at b_lo
            ss = safe_set(e, b_lo, L, n)
            excluded = set(range(n)) - ss

            # Upper excluded (x > (n-1)L)
            upper_exc = []
            for r in excluded:
                x = (e * (r * L + b_lo)) % N
                if x > (n - 1) * L:
                    upper_exc.append(r)

            if not upper_exc:
                continue

            # Formula prediction
            predicted = upper_excluded_residue(e, n)
            checks += 1

            if predicted not in upper_exc:
                print(f"  FORMULA FAIL: n={n}, e={e}, predicted={predicted}, actual_upper={upper_exc}")
                fails += 1
            else:
                # Verify arrival formula: arr = L*(2n-s)/(n*e)
                s = e % n
                expected_arr = L * (2 * n - s) // (n * e)  # should be integer
                actual_arr = arr_time(e, predicted, b_lo, L, n)
                if expected_arr != actual_arr:
                    print(f"  ARR FAIL: n={n}, e={e}, r_high={predicted}, expected_arr={expected_arr}, actual={actual_arr}")
                    fails += 1

    print(f"Checked {checks} (n,e) pairs. Failures: {fails}")


def check_sum_arrivals_bound(n_range=range(3, 8), max_e_factor=3, max_per_n=200):
    """
    Check: sum_r M(r) ≤ n * budget?
    If yes, average M(r) ≤ budget → exists r* with M(r*) ≤ budget.
    """
    def lcm(a, b): return a * b // gcd(a, b)

    def lcm_list(lst):
        r = 1
        for x in lst:
            r = lcm(r, x)
        return r

    print(f"\n{'='*60}")
    print("Checking sum_r M(r) ≤ n*budget (for all tuples with start_run>0)")
    fails_sum = []
    total = 0

    for n in n_range:
        max_e = max_e_factor * n
        target_size = n - 2
        speeds = [e for e in range(1, max_e + 1) if e != n]
        count = 0

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

            b_lo = L // n
            budget = (n - 2) * (L - n) / (2 * n)
            if budget <= 0:
                continue

            safe_sets = {e: safe_set(e, b_lo, L, n) for e in combo}
            from functools import reduce
            Ab = reduce(lambda x, y: x & y, [safe_sets[e] for e in combo]) if combo else frozenset(range(n))
            if Ab:
                count += 1
                continue  # start_run=0

            # Compute M(r) = max_e arr(e,r) for each r
            M = {}
            for r in range(n):
                max_a = 0
                for e in combo:
                    if r not in safe_sets[e]:
                        a = arr_time(e, r, b_lo, L, n)
                        if a > max_a:
                            max_a = a
                M[r] = max_a

            sum_M = sum(M.values())
            n_budget = n * budget
            total += 1
            count += 1

            if sum_M > n_budget:
                fails_sum.append({
                    'n': n, 'E_non': combo, 'L': L,
                    'sum_M': sum_M, 'n_budget': n_budget,
                    'ratio': sum_M / n_budget,
                    'M': M, 'budget': budget,
                })

    print(f"Checked {total} tuples. sum_M > n*budget failures: {len(fails_sum)}")
    if fails_sum:
        for r in fails_sum[:5]:
            print(f"  n={r['n']}, E_non={r['E_non']}: sum_M={r['sum_M']:.1f}, n*budget={r['n_budget']:.1f}, ratio={r['ratio']:.4f}")
    else:
        print("  ✓ sum_M ≤ n*budget for all tested tuples! Average argument works.")

    # Also check: is min_r M(r) ≤ budget?
    return fails_sum


if __name__ == '__main__':
    print("LRC Lemma BR Structure Analysis v1")
    print("=" * 60)

    # Check formula for a_high and arrival time
    check_formula_verification(n_range=range(3, 10))

    # Check sum_r M(r) ≤ n*budget (average argument)
    fails_sum = check_sum_arrivals_bound(n_range=range(3, 8), max_e_factor=3, max_per_n=300)

    # Sweep unit-runner tuples with pigeonhole analysis
    print(f"\n{'='*60}")
    print("Unit-runner pigeonhole sweep")
    results, fails = sweep_unit_tuples(n_range=range(3, 9), max_e_factor=4, max_per_n=300)
