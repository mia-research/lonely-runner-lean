"""
lrc_lemma_br_witness_zone_v1.py

Investigates:
1. For unit-runner tuples with min-exclusion r* (exactly 1 excluding runner e*):
   - Is r* always a LOWER-ZONE excluded residue?
   - When is it upper-zone? What ensures arr ≤ budget then?

2. Algebraic bound for lower-zone witnesses:
   arr(e*, r*) = L*(n-s*)/(n*e*) ≤ budget when e* ≥ 2L*(n-s*)/((n-2)*(L-n))

3. Is the optimal r* (minimizing max_arr) always lower-zone? Always achieves arr ≤ budget?

4. For general (non-unit) tuples: same analysis with gcd-g runners.
"""

from math import gcd
from itertools import combinations


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


def analyze_witness_zone(n, e_non, L):
    """
    For tuple with A_{b_lo}=empty, find all min-exclusion residues and classify:
    - lower zone (x < L) or upper zone (x > (n-1)L)
    - arrival time and budget
    """
    b_lo = L // n
    budget = (n - 2) * (L - n) / (2 * n)
    N = n * L

    safe_sets = {e: safe_set(e, b_lo, L, n) for e in e_non}

    # Verify A_{b_lo} = empty
    from functools import reduce
    Ab = reduce(lambda x, y: x & y, [safe_sets[e] for e in e_non])
    if Ab:
        return None  # start_run = 0

    # For each residue r: list of (e, zone, arr)
    exclusions = {}
    for r in range(n):
        exc = []
        for e in e_non:
            if r not in safe_sets[e]:
                x = x_val(e, r, b_lo, L, n)
                zone = 'lower' if x < L else 'upper'
                arr = arr_time(e, r, b_lo, L, n)
                exc.append((e, zone, arr))
        exclusions[r] = exc

    min_exc = min(len(exclusions[r]) for r in range(n))

    # Find all min-exclusion residues and their zones/arrivals
    min_exc_residues = []
    for r in range(n):
        if len(exclusions[r]) == min_exc:
            exc = exclusions[r]
            if exc:
                max_arr = max(a for _, _, a in exc)
                zone = exc[0][1] if len(exc) == 1 else 'multiple'
                e_star = exc[0][0] if len(exc) == 1 else None
                min_exc_residues.append({
                    'r': r,
                    'zone': zone,
                    'max_arr': max_arr,
                    'e_star': e_star,
                    'ok': max_arr <= budget,
                })
            else:
                min_exc_residues.append({'r': r, 'zone': 'none', 'max_arr': 0, 'e_star': None, 'ok': True})

    # The optimal r* is the one with minimum max_arr
    best = min(min_exc_residues, key=lambda x: x['max_arr'])
    return {
        'min_exc': min_exc,
        'best_r': best['r'],
        'best_zone': best['zone'],
        'best_max_arr': best['max_arr'],
        'budget': budget,
        'ok': best['max_arr'] <= budget,
        'e_star': best['e_star'],
        'all_min': min_exc_residues,
    }


def sweep_zone_analysis(n_range=range(3, 9), max_e_factor=3, max_per_n=300):
    """
    Sweep all tuples (unit and non-unit) and analyze witness zone.
    """
    def lcm(a, b): return a * b // gcd(a, b)
    def lcm_list(lst):
        r = 1
        for x in lst:
            r = lcm(r, x)
        return r

    print(f"\n{'='*64}")
    print("Witness zone analysis sweep")
    print(f"{'='*64}")

    lower_count = 0  # optimal r* in lower zone
    upper_count = 0  # optimal r* in upper zone
    multiple_count = 0  # min_exc > 1
    fails = 0
    total = 0

    # Track: upper-zone witnesses that still satisfy arr ≤ budget
    upper_ok = 0
    upper_fail = 0

    for n in n_range:
        max_e = max_e_factor * n
        target_size = n - 2
        speeds = [e for e in range(1, max_e + 1) if e != n]
        count = 0
        n_upper = 0
        n_lower = 0

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

            r = analyze_witness_zone(n, list(combo), L)
            count += 1
            if r is None:
                continue  # start_run=0

            total += 1
            if r['min_exc'] == 1:
                if r['best_zone'] == 'lower':
                    lower_count += 1
                    n_lower += 1
                elif r['best_zone'] == 'upper':
                    upper_count += 1
                    n_upper += 1
                    if r['ok']:
                        upper_ok += 1
                    else:
                        upper_fail += 1
                        fails += 1
            else:
                multiple_count += 1

            if not r['ok']:
                fails += 1
                print(f"  FAIL: n={n}, E_non={combo}, L={L}: r*={r['best_r']}, zone={r['best_zone']}, "
                      f"arr={r['best_max_arr']:.2f}, budget={r['budget']:.2f}, e*={r['e_star']}")

        if count > 0:
            print(f"  n={n}: lower={n_lower}, upper={n_upper}")

    print(f"\nSummary:")
    print(f"  Total tuples with start_run>0: {total}")
    print(f"  Optimal r* in lower zone: {lower_count} ({100*lower_count/total:.1f}%)")
    print(f"  Optimal r* in upper zone: {upper_count} ({100*upper_count/total:.1f}%)")
    print(f"  Min-exclusion > 1: {multiple_count}")
    print(f"  Upper zone successes: {upper_ok}, failures: {upper_fail}")
    print(f"  TOTAL FAILURES: {fails}")


def algebraic_lower_zone_bound(n_range=range(3, 12)):
    """
    Verify algebraic bound for lower-zone witnesses:
    arr_lower = L*(n-s)/(n*e*), budget = (n-2)(L-n)/(2n)
    arr ≤ budget iff e* ≥ 2*L*(n-s) / ((n-2)*(L-n))
    For L = lcm(e*,n) = e*n (simplest case with gcd(e*,n)=1 and e*>n):
    threshold = 2*e*n*(n-s) / ((n-2)*(e*n-n)) = 2*e*(n-s)/((n-2)*(e*-1))
    """
    print(f"\n{'='*64}")
    print("Algebraic lower-zone bound verification")
    fails = 0

    for n in n_range:
        for e_star in range(1, 4 * n + 1):
            if gcd(e_star, n) != 1:
                continue
            if e_star == n:
                continue
            s = e_star % n
            L = e_star * n  # simplest L = lcm(e*,n) = e*n
            b_lo = L // n  # = e*

            arr_lower = L * (n - s) // (n * e_star)  # should be integer
            budget = (n - 2) * (L - n) / (2 * n)

            if arr_lower > budget:
                fails += 1
                if fails <= 5:
                    print(f"  LOWER BOUND FAIL: n={n}, e*={e_star}, s={s}, L={L}: "
                          f"arr={arr_lower:.2f}, budget={budget:.2f}")

    print(f"Lower zone bound failures (with L=n*e*): {fails}")

    # More general: check for all valid L = lcm(e*,n,k) for small k
    fails2 = 0
    for n in n_range:
        for e_star in range(1, 4 * n + 1):
            if gcd(e_star, n) != 1:
                continue
            if e_star == n:
                continue
            s = e_star % n
            q = e_star // n
            for k in range(1, n + 1):
                L = e_star * n * k
                budget = (n - 2) * (L - n) / (2 * n)
                if budget <= 0:
                    continue
                # a_low for e* with this L
                # x_{e*,a_low}(b_lo) = s*b_lo = s*L/n
                x_low = s * L // n
                arr = (L - x_low) // e_star  # = L*(n-s)/(n*e*)
                if arr > budget:
                    fails2 += 1

    print(f"Lower zone bound failures (with L=n*e*k): {fails2}")


def check_lower_zone_always_valid(n_range=range(3, 9), max_e_factor=3, max_per_n=300):
    """
    Check: For every tuple with start_run>0, there exists r* in the lower zone
    of some unique-excluder runner e* with arr ≤ budget.
    """
    def lcm(a, b): return a * b // gcd(a, b)
    def lcm_list(lst):
        r = 1
        for x in lst:
            r = lcm(r, x)
        return r

    print(f"\n{'='*64}")
    print("Check: lower-zone witness always exists with arr ≤ budget")

    fails = 0
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

            # Check A_{b_lo}=empty
            safe_sets = {e: safe_set(e, b_lo, L, n) for e in combo}
            from functools import reduce
            Ab = reduce(lambda x, y: x & y, [safe_sets[e] for e in combo])
            count += 1
            if Ab:
                continue

            budget = (n - 2) * (L - n) / (2 * n)
            N = n * L
            total += 1

            # For each residue r, compute exclusions
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

            # Find if there's a lower-zone single-exclusion r* with arr ≤ budget
            found_lower_valid = False
            for r in range(n):
                exc = exclusions[r]
                if len(exc) == 1:
                    e, zone, arr = exc[0]
                    if zone == 'lower' and arr <= budget:
                        found_lower_valid = True
                        break

            if not found_lower_valid:
                fails += 1
                if fails <= 3:
                    print(f"  No valid lower-zone witness: n={n}, E_non={combo}, L={L}, budget={budget:.2f}")
                    for r in range(n):
                        exc = exclusions[r]
                        print(f"    r={r}: {[(e,z,a) for e,z,a in exc]}")

    print(f"Tuples checked: {total}. Failures (no valid lower-zone witness): {fails}")


if __name__ == '__main__':
    # 1. Verify algebraic lower-zone bound
    algebraic_lower_zone_bound(n_range=range(3, 10))

    # 2. Sweep zone analysis
    sweep_zone_analysis(n_range=range(3, 9), max_e_factor=3, max_per_n=300)

    # 3. Check if lower-zone witnesses always exist and are valid
    check_lower_zone_always_valid(n_range=range(3, 9), max_e_factor=3, max_per_n=300)
