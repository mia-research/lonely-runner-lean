#!/usr/bin/env python3
"""
lrc_chamber_audit_v1.py
========================
Adversarial audit of the "every chamber is safe under U-FORCE" claim.

A CHAMBER is the maximal interval of fibres b in B_div on which the floor-state
vector (f_e(b))_{e in E_non} is constant.  Safety is constant on each chamber.

Audit goals:
  1. Verify chamber-safety under U-FORCE for all composite n with ≥2 prime
     factors, n = 6..100.  Find any failure.
  2. Find the first n where a chamber is UNSAFE under U-FORCE (falsifies claim).
  3. Separately test non-U-FORCE runner sets: do they produce unsafe chambers?
  4. Check boundary handling (b = n, b = L-n) explicitly.
  5. Compare against brute-force for all testable (n, L).
  6. Report: which runner configurations produce unsafe chambers, if any.

If the chamber-safety claim is true for ALL U-FORCE n tested, record that.
If any counterexample exists, display the full floor-state vector for that chamber.
"""

from math import gcd
from itertools import combinations


# ── arithmetic helpers ──────────────────────────────────────────────────────

def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x


def modinv(a, n):
    g, x, _ = extended_gcd(a % n, n)
    if g != 1:
        raise ValueError
    return x % n


def euler_phi(n):
    result, temp, p = n, n, 2
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0:
                temp //= p
            result -= result // p
        p += 1
    if temp > 1:
        result -= result // temp
    return result


def units_mod_n(n):
    return [e for e in range(1, n) if gcd(e, n) == 1]


def non_units_mod_n(n):
    return [e for e in range(2, n) if gcd(e, n) > 1]


def bad_set(e, t, n):
    """bad(e,t,n) = Sol(e,-t,n) ∪ Sol(e,-(t+1),n)"""
    g = gcd(e, n)
    result = set()
    for j in [-t, -(t + 1)]:
        j_mod = j % n
        if j_mod % g == 0:
            try:
                r0 = (j_mod // g) * modinv(e // g, n // g) % (n // g)
                for k in range(g):
                    result.add((r0 + k * (n // g)) % n)
            except ValueError:
                pass
    return result


def lcm_int(a, b):
    return a * b // gcd(a, b)


def lcm_list(lst):
    r = 1
    for x in lst:
        r = lcm_int(r, x)
    return r


def distinct_prime_factors(n):
    factors, temp, d = set(), n, 2
    while d * d <= temp:
        if temp % d == 0:
            factors.add(d)
            while temp % d == 0:
                temp //= d
        d += 1
    if temp > 1:
        factors.add(temp)
    return factors


# ── chamber analysis ─────────────────────────────────────────────────────────

def chamber_analysis(n, L, E_non, label=""):
    """
    Partition B_div = [n, L-n] into chambers (constant floor-state intervals).
    For each chamber check whether the bad-set union misses some residue.
    Returns list of unsafe chambers (empty list if all are safe).
    """
    b_lo, b_hi = n, L - n
    if b_lo > b_hi:
        return None, []

    # Collect transition points from all runners in E_non
    transition_pts = set([b_lo, b_hi + 1])
    for e in E_non:
        if e <= 1:
            continue
        if L % e != 0:
            # General: transitions where floor(e*b/L) changes
            # This happens at b = ceil(m*L/e)
            f_start = (e * b_lo) // L
            for m in range(f_start + 1, e + 1):
                b_t = (m * L + e - 1) // e  # ceil(mL/e)
                if b_lo <= b_t <= b_hi:
                    transition_pts.add(b_t)
                elif b_t > b_hi:
                    break
        else:
            # Clean z=0 events at exact integer b = mL/e
            for m in range(1, e):
                b_t = m * L // e
                if b_lo <= b_t <= b_hi:
                    transition_pts.add(b_t)

    sorted_pts = sorted(transition_pts)
    unsafe = []
    chambers = []

    for i in range(len(sorted_pts) - 1):
        b_start = sorted_pts[i]
        b_end = sorted_pts[i + 1] - 1
        b_start = max(b_start, b_lo)
        b_end = min(b_end, b_hi)
        if b_start > b_end:
            continue

        width = b_end - b_start + 1
        union_bad = set()
        floor_vec = {}
        for e in E_non:
            f_e = (e * b_start) // L
            floor_vec[e] = f_e
            union_bad |= bad_set(e, f_e, n)

        miss = set(range(n)) - union_bad
        chambers.append({
            'b_start': b_start, 'b_end': b_end, 'width': width,
            'floor_vec': floor_vec, 'miss': miss, 'safe': bool(miss)
        })
        if not miss:
            unsafe.append({
                'b_start': b_start, 'b_end': b_end, 'width': width,
                'floor_vec': floor_vec, 'label': label
            })

    return chambers, unsafe


def brute_force_chambers(n, L, E_non):
    """Brute-force: check every b in B_div independently."""
    b_lo, b_hi = n, L - n
    if b_lo > b_hi:
        return 0
    count = 0
    for b in range(b_lo, b_hi + 1):
        union_bad = set()
        for e in E_non:
            f_e = (e * b) // L
            union_bad |= bad_set(e, f_e, n)
        if set(range(n)) - union_bad:
            count += 1
    return count


# ── audit 1: U-FORCE, all composite n with ≥2 prime factors up to 100 ─────

def audit_uforce(n_max=100):
    print("=" * 80)
    print("AUDIT 1: U-FORCE chamber-safety for all composite n with ≥2 prime factors")
    print(f"Range: n = 6..{n_max}")
    print("=" * 80)

    failures = []
    passes = []

    for n in range(6, n_max + 1):
        if len(distinct_prime_factors(n)) < 2:
            continue

        units = units_mod_n(n)
        active = [e for e in units if e > 1]
        if not active:
            continue

        E_non = units[:]  # U-FORCE: all units active
        L_min = lcm_list(active)

        # Use k=1 (minimal L divisible by all active units)
        L = L_min

        # If B_div is empty, try k=2
        if L <= 2 * n:
            L = 2 * L_min
        if L <= 2 * n:
            continue

        chambers, unsafe = chamber_analysis(n, L, E_non, label=f"n={n},L={L}")

        if unsafe:
            failures.append((n, L, unsafe))
            print(f"  FAIL: n={n}, L={L}: {len(unsafe)} unsafe chambers!")
            for u in unsafe:
                print(f"    Chamber [{u['b_start']},{u['b_end']}], "
                      f"floor_vec={u['floor_vec']}")
        else:
            n_chambers = len(chambers) if chambers else 0
            passes.append(n)

    print()
    if not failures:
        print(f"✓ ALL n in {{6..{n_max}}} with ≥2 prime factors: ZERO unsafe chambers.")
        print(f"  Tested {len(passes)} values of n.")
    else:
        print(f"✗ FAILURES found for n = {[f[0] for f in failures]}")
    return failures


# ── audit 2: vary k (different L sizes) for selected n ─────────────────────

def audit_vary_k(n_list, k_list):
    print()
    print("=" * 80)
    print("AUDIT 2: Vary L (k·lcm) — check chambers for small and large L")
    print("=" * 80)

    for n in n_list:
        units = units_mod_n(n)
        active = [e for e in units if e > 1]
        if not active:
            continue
        E_non = units[:]
        L_min = lcm_list(active)
        phi_n = euler_phi(n)
        bound = sum(e - 1 for e in active)

        print(f"\nn={n}: phi={phi_n}, bound={bound}, lcm={L_min}")
        all_pass = True
        for k in k_list:
            L = k * L_min
            if L <= 2 * n:
                print(f"  k={k}: L={L} ≤ 2n, B_div empty — skip")
                continue
            chambers, unsafe = chamber_analysis(n, L, E_non)
            n_ch = len(chambers) if chambers else 0
            B_safe_ch = sum(c['width'] for c in chambers if c['safe']) if chambers else 0
            if unsafe:
                all_pass = False
                print(f"  k={k:4d}, L={L:>12}: {n_ch} chambers, {len(unsafe)} UNSAFE ✗")
            else:
                # Brute force crosscheck for small L
                if L <= 10000:
                    bf = brute_force_chambers(n, L, E_non)
                    match = "✓" if bf == B_safe_ch else f"MISMATCH(bf={bf})"
                else:
                    match = "(L too large for brute force)"
                print(f"  k={k:4d}, L={L:>12}: {n_ch} chambers, all safe, "
                      f"B_safe={B_safe_ch}/{L-2*n-1}  [{match}]")
        if all_pass:
            print(f"  → All k values: ZERO unsafe chambers for n={n}.")


# ── audit 3: non-U-FORCE runner sets — when do unsafe chambers appear? ─────

def audit_non_uforce(n_list):
    print()
    print("=" * 80)
    print("AUDIT 3: Non-U-FORCE runner sets — find E_non with unsafe chambers")
    print("(Testing: what happens when non-unit runners are added to E_non?)")
    print("=" * 80)

    for n in n_list:
        units = units_mod_n(n)
        non_units = non_units_mod_n(n)
        active_units = [e for e in units if e > 1]
        if not active_units:
            continue
        L = lcm_list(active_units)
        if L <= 2 * n:
            L *= 3

        phi_n = euler_phi(n)
        print(f"\nn={n}: units={units}, non_units={non_units[:8]}")

        # Test 1: U-FORCE (all units only)
        E_uforce = units[:]
        _, unsafe_uf = chamber_analysis(n, L, E_uforce)
        print(f"  U-FORCE (E_non=units):  {len(unsafe_uf)} unsafe chambers")

        # Test 2: Add each non-unit to U-FORCE set
        for nu in non_units[:4]:
            E_test = units[:] + [nu]
            _, unsafe_t = chamber_analysis(n, L, E_test)
            tag = "✗ UNSAFE" if unsafe_t else "✓ safe"
            print(f"  U-FORCE + e={nu} (gcd={gcd(nu,n)},{n}):  "
                  f"{len(unsafe_t)} unsafe chambers  [{tag}]")

        # Test 3: All runners (no drops) — the "full set" case
        E_full = list(range(1, n))
        _, unsafe_full = chamber_analysis(n, L, E_full)
        print(f"  Full E_non={{1..{n-1}}}:  {len(unsafe_full)} unsafe chambers")

        # Test 4: Minimal runner set (just 2 runners)
        if len(units) >= 2:
            E_min = [units[0], units[-1]]  # e.g., {1, n-1}
            _, unsafe_min = chamber_analysis(n, L, E_min)
            print(f"  Minimal E_non={E_min}:  {len(unsafe_min)} unsafe chambers")


# ── audit 4: exact boundary handling ───────────────────────────────────────

def audit_boundaries(n=10):
    print()
    print("=" * 80)
    print(f"AUDIT 4: Exact boundary handling for n={n}")
    print("Verify: fibres b=n and b=L-n are correctly classified")
    print("=" * 80)

    units = units_mod_n(n)
    active = [e for e in units if e > 1]
    E_non = units[:]
    L = lcm_list(active) * 5  # use k=5 to ensure B_div has good width

    b_lo, b_hi = n, L - n
    print(f"B_div = [{b_lo}, {b_hi}], width = {b_hi - b_lo + 1}")

    for b_check in [b_lo, b_lo + 1, b_hi - 1, b_hi]:
        union_bad = set()
        floor_vec = {}
        for e in E_non:
            f_e = (e * b_check) // L
            floor_vec[e] = f_e
            union_bad |= bad_set(e, f_e, n)
        miss = set(range(n)) - union_bad
        print(f"  b={b_check}: floor_vec={floor_vec}  miss={sorted(miss)}  "
              f"{'SAFE' if miss else 'UNSAFE'}")


# ── audit 5: verify the chamber partition logic itself ──────────────────────

def audit_partition_correctness(n=10, k=1):
    """
    Cross-validate: for every b in B_div, check that the chamber containing b
    has the same floor-state vector as the direct computation at b.
    """
    print()
    print("=" * 80)
    print(f"AUDIT 5: Partition correctness — n={n}, k={k}")
    print("Verify floor-state constancy within each chamber via direct check")
    print("=" * 80)

    units = units_mod_n(n)
    active = [e for e in units if e > 1]
    E_non = units[:]
    L = k * lcm_list(active)
    if L <= 2 * n:
        L *= 3

    chambers, unsafe = chamber_analysis(n, L, E_non)
    if chambers is None:
        print("B_div empty")
        return

    errors = 0
    for ch in chambers:
        b_start, b_end = ch['b_start'], ch['b_end']
        for b in range(b_start, min(b_end + 1, b_start + 5)):  # sample up to 5
            for e in E_non:
                f_direct = (e * b) // L
                f_chamber = ch['floor_vec'].get(e, 0)
                if f_direct != f_chamber:
                    print(f"  ERROR: b={b}, e={e}: direct f={f_direct} ≠ chamber f={f_chamber}")
                    errors += 1

    if errors == 0:
        n_chambers = len(chambers)
        print(f"✓ All chamber floor-state assignments verified ({n_chambers} chambers, "
              f"sampled ≤5 fibres each).  ZERO errors.")
    else:
        print(f"✗ {errors} floor-state assignment errors found!")

    # Also verify brute force vs chamber B_safe
    B_safe_ch = sum(c['width'] for c in chambers if c['safe'])
    if L <= 50000:
        B_safe_bf = brute_force_chambers(n, L, E_non)
        match = "✓" if B_safe_bf == B_safe_ch else f"MISMATCH (bf={B_safe_bf})"
        print(f"  Chamber B_safe = {B_safe_ch}, brute-force = {B_safe_bf}  [{match}]")


# ── audit 6: stress test — random E_non configs ─────────────────────────────

def audit_random_stress(n_list, n_trials=50):
    """
    For each n, test n_trials random subsets of {1,...,n-1} as E_non.
    Report any that produce unsafe chambers.
    Goal: find where the claim fails (i.e., understand its boundaries).
    """
    import random
    random.seed(42)

    print()
    print("=" * 80)
    print(f"AUDIT 6: Random E_non stress test ({n_trials} trials per n)")
    print("Goal: find E_non configurations that produce unsafe chambers")
    print("=" * 80)

    for n in n_list:
        candidates = list(range(1, n))
        units = units_mod_n(n)
        active_units = [e for e in units if e > 1]
        if not active_units:
            continue
        L_base = lcm_list(active_units)

        unsafe_configs = []
        for _ in range(n_trials):
            # Random E_non: include at least 2 elements
            size = random.randint(2, len(candidates))
            E_test = sorted(random.sample(candidates, size))

            # L must be divisible by all e in E_test with e > 1
            active_test = [e for e in E_test if e > 1]
            if not active_test:
                continue
            L = lcm_list(active_test)
            if L <= 2 * n:
                L *= 4

            _, unsafe = chamber_analysis(n, L, E_test)
            if unsafe:
                unsafe_configs.append((E_test, L, len(unsafe)))

        if unsafe_configs:
            print(f"  n={n}: {len(unsafe_configs)}/{n_trials} random E_non had unsafe chambers")
            for (E_t, L_t, nu) in unsafe_configs[:3]:
                print(f"    E_non={E_t}, L={L_t}: {nu} unsafe chambers")
                # Check: are all units included?
                has_all_units = all(u in E_t for u in units)
                print(f"    (all units included: {has_all_units})")
        else:
            print(f"  n={n}: 0/{n_trials} random E_non had unsafe chambers  ✓")


# ── main ────────────────────────────────────────────────────────────────────

def main():
    # Audit 1: U-FORCE for all composite n with ≥2 prime factors, n=6..100
    failures = audit_uforce(n_max=100)

    # Audit 2: Vary k for the key n values
    audit_vary_k(
        n_list=[6, 10, 12, 15, 30, 42],
        k_list=[1, 2, 5, 10, 50]
    )

    # Audit 3: Non-U-FORCE sets — find unsafe chambers
    audit_non_uforce(n_list=[6, 10, 12, 15, 30])

    # Audit 4: Boundary handling
    audit_boundaries(n=10)

    # Audit 5: Partition correctness
    audit_partition_correctness(n=15, k=1)

    # Audit 6: Random E_non stress test
    audit_random_stress(n_list=[6, 10, 12, 15, 30], n_trials=100)

    # Final summary
    print()
    print("=" * 80)
    print("FINAL SUMMARY")
    print("=" * 80)
    if not failures:
        print("U-FORCE CLAIM STATUS: ZERO unsafe chambers found for any")
        print("  composite n with ≥2 prime factors in n=6..100.")
        print()
        print("The claim 'every chamber is safe under U-FORCE' survived the audit")
        print("across all tested n.  Chamber-safety appears to be a theorem,")
        print("not just a numerical coincidence.")
        print()
        print("BOUNDARY of the claim (from Audit 3 and 6):")
        print("  Determine whether adding non-unit runners breaks safety,")
        print("  and if so, characterize which E_non configurations are safe.")
    else:
        print(f"FAILURES found at n = {[f[0] for f in failures]}")
        print("The 'every chamber is safe' claim is FALSE — investigate further.")


if __name__ == "__main__":
    main()
