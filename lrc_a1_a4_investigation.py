"""
lrc_a1_a4_investigation.py
===========================
Investigates the TWO remaining enumeration appendices in lrc_proof_v8_2.md:

  A.1 — L=2n edge cases for composite n≤20
  A.4 — prime n≤30, small M (M < M_0)

Goal: identify the MECHANISM for each safe fibre (SOLE_COVER / DUAL_SOLE /
FLOOR_RESET / OTHER) so we can replace enumeration with analytic proofs.

Framework identical to lrc_gap_investigation_v3.py (safe = all runners lonely
at rational time k/n, checked via (e*k) % N ∈ [L, (n-1)*L]).
"""

import sys, math, itertools
from fractions import Fraction
from collections import defaultdict

# ── helpers ────────────────────────────────────────────────────────────────

def euler_phi(n):
    r, t = n, n
    p = 2
    while p*p <= t:
        if t % p == 0:
            while t % p == 0: t //= p
            r -= r // p
        p += 1
    if t > 1: r -= r // t
    return r

def extended_gcd(a, b):
    if a == 0: return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a)*x, x

def mod_inv(a, n):
    g, x, _ = extended_gcd(a % n, n)
    if g != 1: return None
    return x % n

def lcm_list(lst):
    r = 1
    for x in lst: r = math.lcm(r, x)
    return r

def is_prime(n):
    if n < 2: return False
    for p in range(2, int(n**0.5)+1):
        if n % p == 0: return False
    return True

# ── safe-fibre computation (identical to v3) ────────────────────────────────

def x0_and_classify(E_full, n, dropped_unit):
    """Count safe fibres and classify each by mechanism."""
    d = dropped_unit
    L = lcm_list(E_full)
    N = n * L

    d_inv_raw = mod_inv(d, n)
    if d_inv_raw is None:
        return 0, [], L
    d_inv = d_inv_raw
    r_d   = (-d_inv) % n
    s_d   = (d_inv - 1) % n

    I_lo = Fraction(L, n);     I_hi = Fraction(L, n-1)
    J_lo = Fraction((n-2)*L, n-1); J_hi = Fraction((n-1)*L, n)

    reset_map = {}
    for e_u in E_full:
        if math.gcd(e_u, n) != 1: continue
        inv_eu = mod_inv(e_u, n)
        if inv_eu is None: continue
        for m in range(1, e_u):
            num = m * L
            if num % e_u == 0:
                reset_map[num // e_u] = (e_u, m)

    lo, hi = L, (n-1)*L
    safe_list = []
    for k in range(N):
        if not all(lo <= (e*k) % N <= hi for e in E_full):
            continue
        bf = Fraction(k)
        if I_lo <= bf < I_hi:
            mech = "SOLE_COVER"
            det  = f"r_d={r_d}"
        elif J_lo <= bf <= J_hi:
            mech = "DUAL_SOLE"
            det  = f"s_d={s_d}"
        elif k in reset_map:
            e_u, m = reset_map[k]
            if mod_inv(e_u, n):
                dep = (-(m-1)*mod_inv(e_u, n)) % n
            else:
                dep = "?"
            mech = "FLOOR_RESET"
            det  = f"e_u={e_u} m={m}"
        else:
            covered = set()
            for e in E_full:
                t = (e*k)//L
                g = math.gcd(e, n)
                for jneg in (t, t+1):
                    j = (-jneg) % n
                    if j % g == 0:
                        eg, ng, jg = e//g, n//g, j//g
                        inv_eg = mod_inv(eg, ng)
                        if inv_eg is None: continue
                        r0 = (jg * inv_eg) % ng
                        for kk in range(g): covered.add(r0 + kk*ng)
            uncov = sorted(set(range(n)) - covered)
            mech = "OTHER"
            det  = f"uncov={uncov}"
        safe_list.append((k, mech, det))

    return len(safe_list), safe_list, L

# ── A.1 investigation ───────────────────────────────────────────────────────

def run_A1(verbose=False):
    """
    A.1: composite n (all n≤30 composite), canonical tuple E_full={1,...,n}\\{d},
    filter for L = 2n exactly (the cases A.5 SKIPS via L <= 2*n: continue).
    """
    print("\n" + "="*72)
    print("A.1 INVESTIGATION  (composite n, canonical tuple, L = 2n exactly)")
    print("  E_full = {1,...,n} \\ {d};  filter: lcm(E_full) == 2n")
    print("="*72)

    composite_ns = [n for n in range(4, 31) if not is_prime(n)]
    found_any = False

    for n in composite_ns:
        phi_n = euler_phi(n)
        units = [a for a in range(1, n) if math.gcd(a, n) == 1]
        target_L = 2 * n

        cases = []
        for d in units:
            E_full = [r for r in range(1, n+1) if r != d]
            L = lcm_list(E_full)
            if L != target_L:
                continue
            x0, sf, L_act = x0_and_classify(E_full, n, d)
            rec = dict(n=n, d=d, E_full=sorted(E_full), L=L_act,
                       phi_n=phi_n, x0=x0, safe_fibres=sf)
            cases.append(rec)
            found_any = True

        if cases:
            x0s = [c['x0'] for c in cases]
            fails = sum(x < phi_n for x in x0s)
            tight = [c for c in cases if c['x0'] == phi_n]
            print(f"\n── n={n}  φ={phi_n}  L=2n={target_L} ──")
            print(f"  cases={len(cases)}  fails={fails}  "
                  f"x0∈[{min(x0s)},{max(x0s)}]  tight(x0=φ)={len(tight)}")
            for c in cases:
                mechs = {m for (_,m,_) in c['safe_fibres']}
                tally = defaultdict(int)
                for (k,m,det) in c['safe_fibres']: tally[m] += 1
                print(f"  d={c['d']}  x0={c['x0']}  mechs={sorted(mechs)}  "
                      + "  ".join(f"{m}:{cnt}" for m,cnt in sorted(tally.items())))
                if verbose or c['x0'] == phi_n:
                    for (k,m,det) in c['safe_fibres']:
                        b = Fraction(k, n)
                        print(f"    k={k:6d}  b={b}  {m:14s}  {det}")
            # Symmetry check
            for c in cases:
                safe_ks = {k for (k,m,det) in c['safe_fibres']}
                N = n * c['L']
                sym = all((N - k) % N in safe_ks for k in safe_ks)
                print(f"  d={c['d']}: symmetric (k↔N-k)? {sym}")

    if not found_any:
        print("\n  No canonical tuples with L=2n found for any composite n≤30.")
        print("  (This means A.1 covers L=2n cases via NON-canonical tuples.)")
        print("  Running non-canonical enumeration...")
        run_A1_general(verbose=verbose)

def run_A1_general(verbose=False):
    """
    Enumerate ALL speed tuples with n|L and L=2n (not just canonical).
    A tuple is (n-1) speeds from {1,...,2n-1} with lcm=2n, one dropped unit.
    """
    print("\n  [Non-canonical A.1 enumeration]")
    # Only feasible for small n since we enumerate divisor subsets
    for n in [6, 9, 10, 12]:
        phi_n = euler_phi(n)
        target_L = 2 * n
        units_mod_n = [a for a in range(1, n) if math.gcd(a, n) == 1]
        # speeds must divide 2n; find divisors of 2n < 2n
        divs_of_2n = [e for e in range(1, target_L) if target_L % e == 0]
        print(f"\n  n={n}  φ={phi_n}  divisors of 2n={target_L}: {divs_of_2n}")

        # For each dropped unit d not in E:
        found = False
        for d in units_mod_n:
            cands = [e for e in divs_of_2n if e != d]
            # Enumerate subsets of size n-1 from cands with lcm = 2n
            for E in itertools.combinations(cands, n-1):
                if lcm_list(E) != target_L: continue
                x0, sf, _ = x0_and_classify(list(E), n, d)
                if x0 < phi_n:
                    print(f"  FAILURE n={n} d={d} E={sorted(E)} x0={x0} < φ={phi_n}")
                else:
                    if not found:
                        print(f"  n={n}: first valid tuple d={d} E={sorted(E)} x0={x0}")
                    found = True
        if not found:
            print(f"  n={n}: no tuples with lcm=2n and |E|=n-1 found in divisors")

# ── A.4 investigation (extended verbosity) ─────────────────────────────────

def run_A4(verbose=False):
    """
    A.4: prime n≤30, small M < M_0. Extended version: shows full mechanism
    breakdown for ALL cases (not just extremal), to find the analytic pattern.
    """
    print("\n" + "="*72)
    print("A.4 INVESTIGATION  (prime n≤30, small M, full mechanism analysis)")
    print("  E_full = E_non ∪ {n, M};  L = lcm(E_non∪{n}) * M")
    print("="*72)

    prime_ns = [n for n in range(5, 31) if is_prime(n)]
    grand_extremal = []

    for n in prime_ns:
        phi_n = n - 1
        all_res = list(range(1, n))
        print(f"\n── n={n} (prime)  φ={phi_n} ──")

        cases, extremal, has_small_M = [], [], False

        for d1, d2 in itertools.combinations(all_res, 2):
            E_non = [a for a in all_res if a != d1 and a != d2]
            L_0   = lcm_list(E_non + [n])
            M_0   = math.ceil(n*n*(n-1) / (L_0*(n-2)))

            if M_0 <= 1: continue
            has_small_M = True

            for M in range(1, M_0):
                if math.gcd(M, L_0) != 1: continue
                for d in (d1, d2):
                    E_full = E_non + [n, M]
                    if len(set(E_full)) != len(E_full): continue
                    x0, sf, L_act = x0_and_classify(E_full, n, d)
                    mechs = {m for (_,m,_) in sf}
                    tally = defaultdict(int)
                    for (k,m,det) in sf: tally[m] += 1
                    rec = dict(n=n, L=L_act, L_0=L_0, M=M, M_0=M_0,
                               d=d, E_non=sorted(E_non), E_full=sorted(E_full),
                               x0=x0, phi_n=phi_n, safe_fibres=sf,
                               mechs=mechs, tally=dict(tally))
                    cases.append(rec)
                    if x0 < phi_n:
                        print(f"  *** FAILURE x0={x0}<φ  d={d} E_non={sorted(E_non)} M={M}")
                    if x0 == phi_n:
                        extremal.append(rec)

        grand_extremal.extend(extremal)
        if not has_small_M:
            print("  M_0=1 for all configs — fully analytic, no small-M cases.")
            continue

        if not cases:
            print("  No valid small-M cases found.")
            continue

        x0s = [c['x0'] for c in cases]
        M0s = sorted(set(c['M_0'] for c in cases))
        fails = sum(x < phi_n for x in x0s)
        print(f"  cases={len(cases)}  fails={fails}  "
              f"x0∈[{min(x0s)},{max(x0s)}]  extremal={len(extremal)}  M_0 vals={M0s}")

        # Mechanism breakdown across all cases
        mech_counter = defaultdict(int)
        sole_sufficient  = 0   # SOLE_COVER alone gives ≥ phi_n
        dual_sufficient  = 0   # DUAL_SOLE alone gives ≥ phi_n
        reset_present    = 0   # any FLOOR_RESET safe fibre
        other_present    = 0   # any OTHER safe fibre

        for c in cases:
            for m in c['mechs']: mech_counter[m] += 1
            sole_cnt  = c['tally'].get('SOLE_COVER', 0)
            dual_cnt  = c['tally'].get('DUAL_SOLE', 0)
            reset_cnt = c['tally'].get('FLOOR_RESET', 0)
            other_cnt = c['tally'].get('OTHER', 0)
            if sole_cnt >= phi_n:  sole_sufficient  += 1
            if dual_cnt >= phi_n:  dual_sufficient  += 1
            if reset_cnt > 0:      reset_present    += 1
            if other_cnt > 0:      other_present    += 1

        print(f"  Mechanism presence: "
              + ", ".join(f"{m}:{cnt}" for m,cnt in sorted(mech_counter.items())))
        print(f"  SOLE_COVER alone ≥φ in {sole_sufficient}/{len(cases)} cases")
        print(f"  DUAL_SOLE alone  ≥φ in {dual_sufficient}/{len(cases)} cases")
        print(f"  FLOOR_RESET present in {reset_present}/{len(cases)} cases")
        print(f"  OTHER present     in {other_present}/{len(cases)} cases")

        # Show extremal (tight) cases in detail
        if extremal:
            print(f"\n  === Extremal (x0=φ={phi_n}) details ===")
            for c in extremal[:10]:  # cap at 10
                print(f"  n={c['n']} M={c['M']} (M_0={c['M_0']}) L_0={c['L_0']} "
                      f"L={c['L']} d={c['d']} E_non={c['E_non']}")
                print(f"    mechs={sorted(c['mechs'])} tally={c['tally']}")
                if verbose:
                    for (k,m,det) in c['safe_fibres']:
                        b = Fraction(k, n)
                        print(f"      k={k:8d}  b={b}  {m:14s}  {det}")

        # Safe-fibre pattern: do safe ks cluster near I_d or J boundaries?
        if extremal:
            c0 = extremal[0]
            L = c0['L']
            N = n * L
            Ilo_n = L        # I_d lower boundary in k-units: k = n * (L/n) = L
            Ihi_n = L*n//(n-1)
            Jlo_n = (n-2)*L*n//(n-1)
            Jhi_n = (n-1)*L//n * n  # = (n-1)*L (in k-units)
            print(f"\n  First extremal: I_d=[{Ilo_n},{Ihi_n})  J=[{Jlo_n},{Jhi_n}]  N={N}")
            print(f"  Safe k values: {sorted(k for (k,m,det) in c0['safe_fibres'])}")

    print(f"\nTotal extremal across all primes: {len(grand_extremal)}")
    if grand_extremal:
        # Check: what fraction of extremal cases are SOLELY from SOLE_COVER+DUAL_SOLE?
        only_analytic = sum(
            1 for c in grand_extremal
            if not (c['mechs'] - {'SOLE_COVER','DUAL_SOLE'})
        )
        print(f"Extremal with ONLY SOLE_COVER/DUAL_SOLE mechs: "
              f"{only_analytic}/{len(grand_extremal)}")

# ── Extended Safe Window analysis ───────────────────────────────────────────

def check_safe_window_A1(verbose=False):
    """
    For A.1: check whether Safe Window W* = [L/2, (n-1)L/n] gives ≥ φ(n) safe
    fibres at L=2n for dropped unit d=1 (all retained e ≥ 2).
    """
    print("\n" + "="*72)
    print("SAFE WINDOW CHECK for A.1 (d=1, L=2n)")
    print("  W* = [n, 2(n-1)],  |W*∩Z| = n-2;  need n-2 ≥ φ(n) for composite n")
    print("="*72)

    for n in range(4, 25):
        if is_prime(n): continue
        phi_n = euler_phi(n)
        W_size = n - 2  # |W*| = 2(n-1) - n = n-2
        ok = W_size >= phi_n
        # Verify directly: E_full = {2,...,n}\{1} = {2,...,n}
        E_full = list(range(2, n+1))
        L = 2*n
        # Count fibres b in [n, 2(n-1)] that are safe
        # Safe b: for all e, min(e*b mod L, L - e*b mod L) >= L/n = 2
        safe = []
        for b in range(n, 2*(n-1)+1):
            if all(min((e*b) % L, L - (e*b) % L) >= 2 for e in E_full):
                safe.append(b)
        # But L must = lcm(E_full) for the framework; here L=2n is forced
        # Check actual safe count using x0_and_classify with E_full and d=1
        # E_full for d=1 dropped from {1,...,n}: E_full = {2,...,n}, lcm = lcm(2,...,n)
        E_can = list(range(2, n+1))
        L_can = lcm_list(E_can)
        # For the W* argument to apply, we need L_can to divide into W* correctly
        # The key claim is: for L=2n (regardless of actual lcm), W* gives n-2 fibres
        print(f"  n={n}: φ={phi_n}  |W*|=n-2={W_size}  ≥φ? {ok}"
              f"  direct safe in [n,2(n-1)]={len(safe)}"
              f"  (using e*b mod 2n)")

if __name__ == "__main__":
    verbose = "-v" in sys.argv or "--verbose" in sys.argv
    do_a1   = "--a1" in sys.argv
    do_a4   = "--a4" in sys.argv
    do_sw   = "--sw" in sys.argv
    if not do_a1 and not do_a4 and not do_sw:
        do_a1 = do_a4 = do_sw = True

    if do_sw: check_safe_window_A1(verbose=verbose)
    if do_a1: run_A1(verbose=verbose)
    if do_a4: run_A4(verbose=verbose)
