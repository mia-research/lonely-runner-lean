"""
lrc_c02_small_eu_check.py
2026-04-24 — ERR-C-02 Small-e_u Physical Criterion Verification

Verifies the findings from the §2.5 Addendum of lrc_c_err_repair_v1.md:

1. AUTOMATIC GOOD ZONE THEOREM: for runner e' with e_u ∤ e', the position
   {e'·m/e_u} = (e'm mod e_u)/e_u is always in [1/n, (n-1)/n].

2. OBSTRUCTION CHARACTERISATION: only runners with e_u | e' can block
   the isolated event (they have position 0 at every b_m).

3. CASE 1 vs CASE 2: enumeration over composite n, unit e_u, and
   candidate E_non tuples to classify which case applies and whether
   the pacemaker-switch strategy (2a) resolves Case 2.

4. PHYSICAL FREE-m COUNT: for each configuration, count m ∈ {2,...,e_u-1}
   where all runners in E_non are in the good zone.
"""

from math import gcd
from itertools import product
from fractions import Fraction

# ---------------------------------------------------------------------------
# Core utilities
# ---------------------------------------------------------------------------

def is_composite(n):
    if n < 4:
        return False
    for p in range(2, int(n**0.5) + 1):
        if n % p == 0:
            return True
    return False

def units_mod_n(n):
    """All units u in {1,...,n-1} with gcd(u,n)=1."""
    return [u for u in range(1, n) if gcd(u, n) == 1]

def position_at_bm(e_prime, m, e_u):
    """
    Physical position of runner e' at fibre b_m = m*L/e_u:
    {e'·b_m/L} = {e'·m/e_u} = (e'·m mod e_u) / e_u   [as a Fraction]
    """
    residue = (e_prime * m) % e_u
    return Fraction(residue, e_u)

def in_good_zone(pos, n):
    """Check if fractional position pos ∈ [1/n, (n-1)/n]."""
    lo = Fraction(1, n)
    hi = Fraction(n - 1, n)
    return lo <= pos <= hi

def is_free_m(m, e_u, n, E_non):
    """
    Return True if m is a 'free' index: for every runner e' in E_non,
    the position {e'·m/e_u} is in the good zone [1/n,(n-1)/n].
    (Runner e_u itself has position {e_u·m/e_u} = {m} = 0, but it is
    the pacemaker and is intentionally at the zero-crossing.)
    """
    for ep in E_non:
        pos = position_at_bm(ep, m, e_u)
        if not in_good_zone(pos, n):
            return False
    return True

def find_free_ms(e_u, n, E_non):
    """Return list of free m ∈ {2,...,e_u-1}."""
    return [m for m in range(2, e_u) if is_free_m(m, e_u, n, E_non)]

def has_eu_divides(e_u, E_non):
    """Return subset of E_non where e_u | e'."""
    return [ep for ep in E_non if ep % e_u == 0]

# ---------------------------------------------------------------------------
# Part 1: Verify the CORRECT Good Zone Lemma: e_u ∤ e'·m → position ∈ [1/n,(n-1)/n]
# ---------------------------------------------------------------------------

def verify_good_zone_lemma(n_max=20):
    """
    Correct lemma: {e'·m/e_u} ∈ [1/n,(n-1)/n] iff e_u ∤ e'·m.
    Verify both directions for all composite n ≤ n_max.
    """
    print("=" * 60)
    print("PART 1: Good Zone Lemma Verification (CORRECTED)")
    print("  {e'm/e_u} ∈ [1/n,(n-1)/n]  iff  e_u ∤ e'm")
    print("=" * 60)
    failures_fwd = []   # e_u ∤ e'm but NOT in good zone
    failures_bwd = []   # e_u | e'm but IS in good zone (would be pos=0, not in good zone)
    total_checks = 0

    for n in range(4, n_max + 1):
        if not is_composite(n):
            continue
        for e_u in range(2, n):
            if gcd(e_u, n) != 1:
                continue
            for ep in range(1, 4 * n):
                if ep == e_u:
                    continue
                for m in range(1, e_u):
                    total_checks += 1
                    pos = position_at_bm(ep, m, e_u)
                    divides = ((ep * m) % e_u == 0)
                    good = in_good_zone(pos, n)

                    if not divides and not good:
                        failures_fwd.append((n, e_u, ep, m, float(pos)))
                    if divides and good:
                        failures_bwd.append((n, e_u, ep, m, float(pos)))

    if failures_fwd or failures_bwd:
        if failures_fwd:
            print(f"  FWD FAILURES (e_u∤e'm but not good zone): {len(failures_fwd)}")
            for f in failures_fwd[:5]:
                print(f"    n={f[0]}, e_u={f[1]}, e'={f[2]}, m={f[3]}, pos={f[4]:.4f}")
        if failures_bwd:
            print(f"  BWD FAILURES (e_u|e'm but in good zone): {len(failures_bwd)}")
    else:
        print(f"  LEMMA VERIFIED: {total_checks} checks, 0 failures.")
        print("  The iff holds: e_u∤e'm ↔ position ∈ [1/n,(n-1)/n].")

    # Also verify the bad-m count formula: gcd(e',e_u)-1 per runner
    print()
    print("  Verifying bad-m count formula per runner: |bad m| = gcd(e',e_u)-1")
    count_failures = 0
    count_total = 0
    for n in [6, 9, 12, 15]:
        if not is_composite(n):
            continue
        for e_u in [eu for eu in range(2, n) if gcd(eu, n) == 1 and eu >= 3]:
            for ep in range(1, 3 * n):
                if ep == e_u:
                    continue
                count_total += 1
                g = gcd(ep, e_u)
                expected_bad = g - 1
                actual_bad = sum(1 for m in range(2, e_u) if (ep * m) % e_u == 0)
                if actual_bad != expected_bad:
                    count_failures += 1
                    if count_failures <= 3:
                        print(f"    MISMATCH: n={n}, e_u={e_u}, e'={ep}, "
                              f"gcd={g}, expected_bad={expected_bad}, actual_bad={actual_bad}")
    if count_failures == 0:
        print(f"  Bad-m count formula verified: {count_total} (e_u,e') pairs, 0 mismatches.")
    print()

# ---------------------------------------------------------------------------
# Part 2: Confirm e_u | e' runners are at position 0
# ---------------------------------------------------------------------------

def verify_eu_divisible_at_zero(n_max=20):
    """
    For all composite n, unit e_u, runner e' with e_u | e':
    confirm {e'·m/e_u} = 0 for all m ∈ {1,...,e_u-1}.
    """
    print("=" * 60)
    print("PART 2: e_u | e' → Position Always 0")
    print("=" * 60)
    failures = []
    total_checks = 0

    for n in range(4, n_max + 1):
        if not is_composite(n):
            continue
        for e_u in range(2, n):
            if gcd(e_u, n) != 1:
                continue
            # Check multiples of e_u up to 4n
            for k in range(1, int(4 * n / e_u) + 1):
                ep = k * e_u
                for m in range(1, e_u):
                    total_checks += 1
                    pos = position_at_bm(ep, m, e_u)
                    if pos != 0:
                        failures.append((n, e_u, ep, m, float(pos)))

    if failures:
        print(f"  FAILURES ({len(failures)} / {total_checks} checks):")
        for f in failures[:10]:
            print(f"    n={f[0]}, e_u={f[1]}, e'={f[2]}, m={f[3]}, pos={f[4]}")
    else:
        print(f"  CONFIRMED: {total_checks} checks, 0 failures.")
        print("  All e_u-multiple runners have position 0 at every b_m.")
    print()

# ---------------------------------------------------------------------------
# Part 3: Enumerate Case 1 vs Case 2 in practice
# ---------------------------------------------------------------------------

def classify_configurations(n_values=None, speed_bound=None):
    """
    For composite n in n_values, enumerate E_non configurations and
    classify Case 1 (no e_u|e' in E_non) vs Case 2 (some e_u|e').
    For Case 2: check pacemaker-switch strategy.
    """
    if n_values is None:
        n_values = [4, 6, 8, 9, 10, 12, 15]
    if speed_bound is None:
        speed_bound = 30

    print("=" * 60)
    print("PART 3: Case 1 / Case 2 Classification")
    print("=" * 60)

    for n in n_values:
        if not is_composite(n):
            continue
        print(f"\n  n = {n}")
        all_units = units_mod_n(n)

        for e_u in all_units:
            # Candidate E_non: all speeds 1..speed_bound except e_u
            all_candidates = [e for e in range(1, speed_bound + 1) if e != e_u]

            # Divisible runners (potential Case 2 triggers)
            div_runners = [ep for ep in all_candidates if ep % e_u == 0]
            # Non-divisible runners (always safe)
            nondiv_runners = [ep for ep in all_candidates if ep % e_u != 0]

            if not div_runners:
                print(f"    e_u={e_u}: No e_u-multiple runners up to {speed_bound}. Always Case 1.")
                continue

            # Example Case 2: E_non with the smallest e_u-multiple
            # (The obstruction runner e'_obs = (n-1)*e_u)
            e_obs = (n - 1) * e_u
            if e_obs <= speed_bound:
                # Check: does e_obs have rho' = u ?
                rho_obs = e_obs % n
                u = n - e_u
                is_genuine_obstruction = (rho_obs == u)

                # Count free m with E_non = {e_obs}
                free_ms = find_free_ms(e_u, n, [e_obs])
                status_obs = "BLOCKED (0 free m)" if not free_ms else f"FREE: {free_ms}"

                # Pacemaker switch: try all other unit runners as pacemaker
                alt_pacemakers = []
                for e_star in all_units:
                    if e_star == e_u:
                        continue
                    if e_obs % e_star != 0:  # e_star does NOT divide e_obs
                        # Under e_star as pacemaker: e_obs is in good zone
                        # (by Automatic Good Zone Thm applied to e_star)
                        # Need range {2,...,e_star-1} to be non-empty
                        if e_star >= 3:
                            alt_pacemakers.append(e_star)

                print(f"    e_u={e_u}, e'_obs={(n-1)*e_u} (rho'={rho_obs}, u={u}): "
                      f"{'genuine obstruction' if is_genuine_obstruction else 'not obstruction (rho!=u)'}. "
                      f"free-m with E_non={{e_obs}}: {status_obs}. "
                      f"Alt pacemakers (e_u∤e_obs): {alt_pacemakers[:5]}")

# ---------------------------------------------------------------------------
# Part 4: Physical free-m count for random/adversarial E_non
# ---------------------------------------------------------------------------

def free_m_statistics(n_values=None, speed_bound=None, sample_size=None):
    """
    For composite n, e_u, and random/adversarial E_non with up to n-2 runners
    from 1..speed_bound: count free m values under physical criterion.
    """
    import random
    random.seed(42)

    if n_values is None:
        n_values = [6, 9, 10, 12, 15]
    if speed_bound is None:
        speed_bound = 50
    if sample_size is None:
        sample_size = 200

    print("=" * 60)
    print("PART 4: Physical Free-m Count Statistics")
    print("  (Physical criterion: position ∈ [1/n,(n-1)/n])")
    print("=" * 60)

    for n in n_values:
        if not is_composite(n):
            continue
        all_units = units_mod_n(n)
        print(f"\n  n={n}, units={all_units}")

        for e_u in all_units[:3]:  # Check first few unit pacemakers
            zero_free = 0
            total_configs = 0
            min_free_count = e_u - 2
            min_config = None

            candidates = [e for e in range(1, speed_bound + 1) if e != e_u]
            max_size = min(n - 2, len(candidates))

            for _ in range(sample_size):
                size = random.randint(1, max_size)
                E_non = random.sample(candidates, size)
                free_ms = find_free_ms(e_u, n, E_non)

                if len(free_ms) < min_free_count:
                    min_free_count = len(free_ms)
                    min_config = (E_non[:], free_ms[:])

                if len(free_ms) == 0:
                    zero_free += 1
                total_configs += 1

            # Also check adversarial case: E_non = all e_u-multiples in range
            eu_multiples = [k * e_u for k in range(2, speed_bound // e_u + 1)]
            if eu_multiples:
                adv_free = find_free_ms(e_u, n, eu_multiples[:min(n-2, len(eu_multiples))])
            else:
                adv_free = list(range(2, e_u))

            print(f"    e_u={e_u}, range_size={e_u-2}: "
                  f"zero-free configs: {zero_free}/{total_configs}, "
                  f"min_free={min_free_count}. "
                  f"Adversarial (only e_u-multiples): {len(adv_free)} free m")

            if zero_free > 0 and min_config:
                print(f"      ZERO-FREE example: E_non={min_config[0][:8]} "
                      f"(contains e_u-multiples: {[e for e in min_config[0] if e%e_u==0]})")

# ---------------------------------------------------------------------------
# Part 5: Confirm no e_u-multiple runner is a unit with rho'=u
# for small n (checking whether theorem hypotheses exclude Case 2)
# ---------------------------------------------------------------------------

def check_case2_unit_rho(n_max=20):
    """
    For each composite n and each unit e_u:
    - Find the minimal obstruction runner e_obs = (n-1)*e_u
    - Check if e_obs is a unit runner (gcd(e_obs, n) = 1) with rho'=u
    - This determines whether Case 2 is physically realizable.
    """
    print("=" * 60)
    print("PART 5: Obstruction Runner Properties")
    print(f"  e'_obs = (n-1)*e_u, u = n-e_u")
    print("=" * 60)
    print(f"  {'n':>4} {'e_u':>5} {'u':>4} {'e_obs':>7} {'rho_obs':>8} {'gcd(e_obs,n)':>13} {'unit?':>6} {'rho=u?':>7}")
    print("  " + "-"*60)

    for n in range(4, n_max + 1):
        if not is_composite(n):
            continue
        for e_u in units_mod_n(n):
            u = n - e_u
            e_obs = (n - 1) * e_u
            rho_obs = e_obs % n
            g = gcd(e_obs, n)
            is_unit = (g == 1)
            rho_eq_u = (rho_obs == u)
            # Flag the genuine obstruction cases
            flag = " <-- CASE 2" if (is_unit and rho_eq_u) else ""
            print(f"  {n:>4} {e_u:>5} {u:>4} {e_obs:>7} {rho_obs:>8} {g:>13} {str(is_unit):>6} {str(rho_eq_u):>7}{flag}")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    print()
    print("ERR-C-02 Small-e_u Verification Suite")
    print("lrc_c02_small_eu_check.py — 2026-04-24")
    print()

    ok = verify_good_zone_lemma(n_max=18)

    verify_eu_divisible_at_zero(n_max=18)

    check_case2_unit_rho(n_max=16)

    classify_configurations(
        n_values=[4, 6, 8, 9, 10, 12],
        speed_bound=60,
    )

    free_m_statistics(
        n_values=[6, 9, 10, 12],
        speed_bound=50,
        sample_size=300,
    )

    print()
    print("Done.")
