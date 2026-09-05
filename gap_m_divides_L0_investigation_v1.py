"""
gap_m_divides_L0_investigation_v1.py
=====================================
Investigates the analytic gap in Proposition 10.5 (Tier 2, prime n >= 11):
the period-decomposition argument fails when the free runner M satisfies M | L0.

Four phases (select via --phase, default: 1 3):
  1  Canonical enumeration  -> gap_degenerate_canonical_results.csv
  2  Non-canonical sweep    -> gap_degenerate_noncanon_results.csv
  3  Mechanism classification -> gap_degenerate_mechanisms.csv
  4  Outlier drill-down     -> stdout

Functions copied from lrc_gap_deep_v1.py (no import dependency).
"""

import sys, math, itertools, csv
from fractions import Fraction
from math import gcd, floor, ceil
from collections import defaultdict

# ── utilities (copied from lrc_gap_deep_v1.py) ───────────────────────────────

def euler_phi(n):
    r, t = n, n
    p = 2
    while p * p <= t:
        if t % p == 0:
            while t % p == 0: t //= p
            r -= r // p
        p += 1
    if t > 1: r -= r // t
    return r

def extended_gcd(a, b):
    if a == 0: return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def mod_inv(a, n):
    g, x, _ = extended_gcd(a % n, n)
    assert g == 1, f"mod_inv: gcd({a},{n}) != 1"
    return x % n

def lcm_list(lst):
    r = 1
    for x in lst: r = math.lcm(r, x)
    return r

def is_prime(n):
    if n < 2: return False
    for p in range(2, int(n**0.5) + 1):
        if n % p == 0: return False
    return True

def x0_count(E_full, n):
    """Count safe fibres: k in {0,...,nL-1} with L <= e*k mod nL <= (n-1)*L for all e."""
    L = lcm_list(E_full)
    N = n * L
    lo, hi = L, (n - 1) * L
    count = sum(1 for k in range(N) if all(lo <= (e * k) % N <= hi for e in E_full))
    return count, L

def x0_classified(E_full, n, d):
    """x0 with mechanism labels: SOLE_COVER / DUAL_SOLE / FLOOR_RESET / OTHER."""
    L = lcm_list(E_full)
    N = n * L
    lo, hi = L, (n - 1) * L

    d_inv = mod_inv(d, n)
    r_d   = (-d_inv) % n
    s_d   = (d_inv - 1) % n

    I_lo = Fraction(L, n);       I_hi = Fraction(L, n - 1)
    J_lo = Fraction((n - 2) * L, n - 1); J_hi = Fraction((n - 1) * L, n)

    reset_map = {}
    for e in E_full:
        if gcd(e, n) != 1: continue
        for m in range(1, e):
            if (m * L) % e == 0:
                reset_map[(m * L) // e] = (e, m)

    safe = []
    for k in range(N):
        if not all(lo <= (e * k) % N <= hi for e in E_full):
            continue
        bf = Fraction(k)
        if I_lo <= bf < I_hi:
            mech = "SOLE_COVER"
        elif J_lo <= bf <= J_hi:
            mech = "DUAL_SOLE"
        elif k in reset_map:
            mech = "FLOOR_RESET"
        else:
            mech = "OTHER"
        safe.append((k, mech))
    return len(safe), safe, L

def sole_cover_interval_count(L, n):
    """Integer count of I_d = [L/n, L/(n-1)): floor(L/(n-1)) - ceil(L/n) + 1."""
    lo = math.ceil(L / n)
    hi = math.floor(L / (n - 1))
    return max(0, hi - lo + 1)

# ── enumeration ───────────────────────────────────────────────────────────────

PRIMES = [11, 13, 17, 19, 23, 29]

def enumerate_degenerate(n):
    """
    For prime n, enumerate all (dropped_unit, M_res, E_non_res, L0, d) where
    M_res | L0 and M_res >= 3.  Uses canonical speeds (speed = residue).
    """
    results = []
    residues = list(range(1, n))
    for drop1, drop2 in itertools.combinations(residues, 2):
        for dropped_unit, M_res in [(drop1, drop2), (drop2, drop1)]:
            E_non_res = sorted(set(residues) - {dropped_unit, M_res})
            L0 = lcm_list(E_non_res)
            d  = gcd(M_res, L0)
            if d == M_res and M_res >= 3:
                results.append({
                    'n': n,
                    'dropped_unit': dropped_unit,
                    'M_res': M_res,
                    'E_non_res': E_non_res,
                    'L0': L0,
                    'd': d,
                })
    return results

# ── Phase 1 ───────────────────────────────────────────────────────────────────

def phase1():
    print("\n=== PHASE 1: Canonical enumeration ===")
    rows = []
    failures = []

    for n in PRIMES:
        phi = euler_phi(n)
        families = enumerate_degenerate(n)
        print(f"  n={n}: {len(families)} degenerate families found")
        for fam in families:
            E_full = fam['E_non_res'] + [fam['M_res'], n]
            x0, L = x0_count(E_full, n)
            passes = (x0 >= phi)
            row = {
                'n': n,
                'dropped_unit': fam['dropped_unit'],
                'M_res': fam['M_res'],
                'E_non_res': str(fam['E_non_res']),
                'L0': fam['L0'],
                'd': fam['d'],
                'L': L,
                'x0': x0,
                'phi_n': phi,
                'passes': passes,
            }
            rows.append(row)
            if not passes:
                failures.append(row)
                print(f"  *** FAILURE: n={n} du={fam['dropped_unit']} M={fam['M_res']} "
                      f"L0={fam['L0']} x0={x0} phi={phi}")

    with open('gap_degenerate_canonical_results.csv', 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()) if rows else [])
        w.writeheader(); w.writerows(rows)

    print(f"\n  Total families: {len(rows)}")
    print(f"  Failures (x0 < phi(n)): {len(failures)}")
    print(f"  Written: gap_degenerate_canonical_results.csv")
    return rows, failures

# ── Phase 2 ───────────────────────────────────────────────────────────────────

def phase2():
    print("\n=== PHASE 2: Non-canonical sweep ===")
    try:
        with open('gap_degenerate_canonical_results.csv') as f:
            canon_rows = list(csv.DictReader(f))
    except FileNotFoundError:
        print("  Run Phase 1 first."); return

    out_rows = []
    COMBO_LIMIT = 50000
    REP_CAP_MULT = 5

    for cr in canon_rows:
        n         = int(cr['n'])
        du        = int(cr['dropped_unit'])
        M_res     = int(cr['M_res'])
        phi       = int(cr['phi_n'])
        rep_cap   = REP_CAP_MULT * n
        import ast
        E_non_res = ast.literal_eval(cr['E_non_res'])

        # Candidate representatives for each residue
        all_res = E_non_res + [M_res]
        candidates = {}
        for r in all_res:
            reps = [r + k * n for k in range(0, (rep_cap // n) + 1) if r + k * n > 0
                    and gcd(r + k * n, n) == 1]
            candidates[r] = reps[:max(1, rep_cap // n)]

        min_x0 = int(cr['x0'])
        combos_tried = 0

        combo_gen = itertools.product(*[candidates[r] for r in all_res])
        for combo in combo_gen:
            if combos_tried >= COMBO_LIMIT:
                break
            combos_tried += 1
            E_full_nc = list(combo) + [n]
            if gcd(*E_full_nc) != 1:
                continue
            x0_nc, _ = x0_count(E_full_nc, n)
            if x0_nc < min_x0:
                min_x0 = x0_nc

        out_rows.append({
            'n': n,
            'dropped_unit': du,
            'M_res': M_res,
            'L0_canon': cr['L0'],
            'combos_tried': combos_tried,
            'min_x0': min_x0,
            'phi_n': phi,
            'passes': min_x0 >= phi,
        })
        print(f"  n={n} du={du} M={M_res}: min_x0={min_x0} phi={phi} "
              f"({'PASS' if min_x0 >= phi else 'FAIL'}) [{combos_tried} combos]")

    with open('gap_degenerate_noncanon_results.csv', 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(out_rows[0].keys()) if out_rows else [])
        w.writeheader(); w.writerows(out_rows)

    failures = [r for r in out_rows if not r['passes']]
    print(f"\n  Total families: {len(out_rows)}")
    print(f"  Failures (min_x0 < phi): {len(failures)}")
    print(f"  Written: gap_degenerate_noncanon_results.csv")

# ── Phase 3 ───────────────────────────────────────────────────────────────────

def phase3():
    print("\n=== PHASE 3: Mechanism classification ===")
    try:
        with open('gap_degenerate_canonical_results.csv') as f:
            canon_rows = list(csv.DictReader(f))
    except FileNotFoundError:
        print("  Run Phase 1 first."); return

    out_rows = []
    import ast

    for cr in canon_rows:
        n         = int(cr['n'])
        du        = int(cr['dropped_unit'])
        M_res     = int(cr['M_res'])
        phi       = int(cr['phi_n'])
        E_non_res = ast.literal_eval(cr['E_non_res'])
        E_full    = E_non_res + [M_res, n]

        count, safe_list, L = x0_classified(E_full, n, du)
        mech_counts = defaultdict(int)
        for _, mech in safe_list:
            mech_counts[mech] += 1

        icount = sole_cover_interval_count(L, n)
        L0     = int(cr['L0'])
        threshold_sq = (n - 1) ** 2   # Candidate Lemma threshold: L0 >= (n-1)^2?

        out_rows.append({
            'n': n,
            'dropped_unit': du,
            'M_res': M_res,
            'L0': L0,
            'L': L,
            'x0': count,
            'phi_n': phi,
            'SOLE_COVER': mech_counts['SOLE_COVER'],
            'DUAL_SOLE': mech_counts['DUAL_SOLE'],
            'FLOOR_RESET': mech_counts['FLOOR_RESET'],
            'OTHER': mech_counts['OTHER'],
            'interval_count': icount,
            'L0_ge_threshold': L0 >= threshold_sq,
            'interval_ge_phi': icount >= phi,
        })

    with open('gap_degenerate_mechanisms.csv', 'w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(out_rows[0].keys()) if out_rows else [])
        w.writeheader(); w.writerows(out_rows)

    # Summary stats
    sc_always_enough = all(r['SOLE_COVER'] >= int(r['phi_n']) for r in out_rows)
    interval_always_enough = all(r['interval_ge_phi'] for r in out_rows)
    L0_threshold_holds = all(r['L0_ge_threshold'] for r in out_rows)

    print(f"  Total families: {len(out_rows)}")
    print(f"  SOLE_COVER alone >= phi(n): {sc_always_enough}")
    print(f"  Interval count alone >= phi(n): {interval_always_enough}")
    print(f"  L0 >= (n-1)^2 always: {L0_threshold_holds}")

    # Breakdown by n
    for n in PRIMES:
        nrows = [r for r in out_rows if r['n'] == n]
        if not nrows: continue
        avg_sc = sum(r['SOLE_COVER'] for r in nrows) / len(nrows)
        avg_tot = sum(r['x0'] for r in nrows) / len(nrows)
        print(f"  n={n}: {len(nrows)} families, avg_x0={avg_tot:.1f}, "
              f"avg_SOLE_COVER={avg_sc:.1f}, phi={euler_phi(n)}")

    print(f"  Written: gap_degenerate_mechanisms.csv")
    return out_rows

# ── Phase 4 ───────────────────────────────────────────────────────────────────

def phase4():
    print("\n=== PHASE 4: Outlier drill-down ===")
    try:
        with open('gap_degenerate_mechanisms.csv') as f:
            mech_rows = list(csv.DictReader(f))
    except FileNotFoundError:
        print("  Run Phase 3 first."); return

    import ast

    # Sort by x0 ascending, take bottom 10% (min 3)
    mech_rows.sort(key=lambda r: int(r['x0']))
    n_outliers = max(3, len(mech_rows) // 10)
    outliers = mech_rows[:n_outliers]

    print(f"  Examining {n_outliers} tightest families (of {len(mech_rows)} total):\n")

    for r in outliers:
        n          = int(r['n'])
        du         = int(r['dropped_unit'])
        M_res      = int(r['M_res'])
        phi        = int(r['phi_n'])
        L0         = int(r['L0'])
        L          = int(r['L'])
        x0         = int(r['x0'])
        icount     = int(r['interval_count'])
        threshold  = (n - 1) ** 2
        sc         = int(r['SOLE_COVER'])

        print(f"  ─── n={n}, dropped_unit={du}, M_res={M_res} ───")
        print(f"      L0={L0}, L={L}, x0={x0}, phi={phi}")
        print(f"      SOLE_COVER={sc}, DUAL_SOLE={r['DUAL_SOLE']}, "
              f"FLOOR_RESET={r['FLOOR_RESET']}, OTHER={r['OTHER']}")
        print(f"      I_d interval count = {icount}  (need >= {phi}): "
              f"{'OK' if icount >= phi else 'INSUFFICIENT'}")
        print(f"      L0 >= (n-1)^2 = {threshold}? {L0} >= {threshold}: "
              f"{'YES' if L0 >= threshold else 'NO'}")
        print(f"      L/n(n-1) = {L}/({n}*{n-1}) = {Fraction(L, n*(n-1))} "
              f">= n-1={n-1}? {'YES' if Fraction(L, n*(n-1)) >= n-1 else 'NO'}")

        # Re-run classification for full detail
        with open('gap_degenerate_canonical_results.csv') as f2:
            canon = {(int(rr['n']), int(rr['dropped_unit']), int(rr['M_res'])): rr
                     for rr in csv.DictReader(f2)}
        key = (n, du, M_res)
        if key in canon:
            E_non_res = ast.literal_eval(canon[key]['E_non_res'])
            E_full    = E_non_res + [M_res, n]
            _, safe_list, _ = x0_classified(E_full, n, du)
            print(f"      Safe fibres ({len(safe_list)} total):")
            for k, mech in safe_list:
                print(f"        k={k:6d}  {mech}")
        print()

# ── main ──────────────────────────────────────────────────────────────────────

if __name__ == '__main__':
    args = sys.argv[1:]
    phases = []
    i = 0
    while i < len(args):
        if args[i] == '--phase':
            i += 1
            while i < len(args) and args[i].isdigit():
                phases.append(int(args[i])); i += 1
        else:
            i += 1
    if not phases:
        phases = [1, 3]

    print(f"Running phases: {phases}")

    if 1 in phases:
        phase1()
    if 2 in phases:
        phase2()
    if 3 in phases:
        phase3()
    if 4 in phases:
        phase4()
