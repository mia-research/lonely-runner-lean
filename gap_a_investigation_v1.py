"""
gap_a_investigation_v1.py
=========================
Exhaustive search for exceptions, outliers, and near-counterexamples in Gap A.

GAP A (precise statement):
  For the Z0S bound to give B_safe ≥ 1, we need at least one z=0 event with m≥2
  where r_dep is NOT covered by any other runner in E_fix via Cond1/Cond2.
  Empirically true, analytically unproven.

KEY QUESTION: Find (n, E_fix, e_u, m) where ALL m≥2 z=0 events are covered
              (isolated count = 0) — would be a "Gap A counterexample candidate".
              Then investigate WHY such cases do or don't arise.

Cond1/Cond2 (from z0s_discrepancy_analysis_v1.py, proved with 0 discrepancies):
  At z=0 event m of unit runner e_u (r_dep = -(m-1)·e_u^{-1} mod n):
  s := e'·m mod e_u
  e' covers r_dep  iff  s = e'  [Cond1, requires e' < e_u]
                    OR  (e' + e_u ≥ n AND s = e' + e_u - n)  [Cond2]

SEARCH PLAN:
  Part 1: Pure unit relay — E_fix = all units of Z_n. Find (n, e_u, m) with m≥2
          where neither Cond1 nor Cond2 fires for ANY unit e'.
          Find n where isolated count = 0 (no isolated events at all).

  Part 2: Impact of non-unit runners — add non-unit runners to E_fix, check if
          they systematically cover r_dep (which would reduce isolated count further).
          Find minimum isolated count across all valid E configurations.

  Part 3: Tight cases — for each n, which (e_u, m) pair has the FEWEST covering
          runners? Understand the structure of nearly-isolated events.

  Part 4: Systematic structure — for a fixed n, map which (e_u, m) pairs are
          isolated vs covered. Look for patterns (arithmetic progressions, etc.).

  Part 5: Large n search — extend to n up to 100 to see if isolated count ever hits 0.
"""

from math import gcd
from itertools import combinations

def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def modinv(a, n):
    g, x, _ = extended_gcd(a % n, n)
    if g != 1:
        return None
    return x % n

def phi(n):
    result, temp = n, n
    p = 2
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

def nonunits_mod_n(n):
    return [e for e in range(1, n) if gcd(e, n) > 1]

def bad_set(e, t, n):
    """Bad set of runner e at floor t: residues r where floor changes at α near t/e.
    bad(e,t,n) = Sol(e,-t,n) ∪ Sol(e,-(t+1),n)
    For unit e: each Sol is a singleton; for non-unit: empty or full coset."""
    g = gcd(e, n)
    result = set()
    # Sol(e, -t, n): e·r ≡ -t (mod n), i.e., (e/g)·r ≡ -t/g (mod n/g)
    if t % g == 0:
        # Solution exists
        eg, ng = e // g, n // g
        inv_eg = modinv(eg, ng)
        if inv_eg is not None:
            r0 = ((-t // g) * inv_eg) % ng
            for k in range(g):
                result.add(r0 + k * ng)
    # Sol(e, -(t+1), n)
    tp1 = t + 1
    if tp1 % g == 0:
        eg, ng = e // g, n // g
        inv_eg = modinv(eg, ng)
        if inv_eg is not None:
            r0 = ((-tp1 // g) * inv_eg) % ng
            for k in range(g):
                result.add(r0 + k * ng)
    return result

def covers_via_cond(ep, eu, m):
    """Check if runner e' covers r_dep at z=0 event m of e_u via Cond1 or Cond2.
    Cond1: s = e'  (s = e'·m mod e_u, requires e' < e_u)
    Cond2: e' + e_u >= n AND s = e' + e_u - n  (but this needs n as parameter)
    Returns True/False and which condition fired."""
    s = (ep * m) % eu
    if ep < eu and s == ep:
        return True, 1
    return False, 0

def covers_via_cond_with_n(ep, eu, m, n):
    """Full Cond1/Cond2 check including n."""
    s = (ep * m) % eu
    # Cond1
    if ep < eu and s == ep:
        return True, 1
    # Cond2: e' + e_u >= n and s = e' + e_u - n
    if ep + eu >= n and s == (ep + eu - n):
        return True, 2
    return False, 0

def covers_via_bad_set(ep, eu, m, r_dep, n):
    """Check if runner e' covers r_dep at b_m = m*L/eu using the bad set directly.
    Floor of e' at b_m: t_ep = floor(e' * m / e_u).
    r_dep in bad(e', t_ep, n)."""
    t_ep = (ep * m) // eu
    bs = bad_set(ep, t_ep, n)
    return r_dep in bs

def compute_r_dep(eu, m, n):
    """r_dep for z=0 event m of unit runner e_u.
    r_dep = -(m-1) * e_u^{-1} mod n."""
    inv_eu = modinv(eu, n)
    if inv_eu is None:
        return None
    return (-(m - 1) * inv_eu) % n

def analyze_n(n, e_fix_nonunits=None, verbose=False):
    """For given n and optional non-unit runners in E_fix,
    find all z=0 events with m>=2, classify each as isolated or covered.

    Returns dict with summary statistics."""
    units = units_mod_n(n)
    if e_fix_nonunits is None:
        e_fix_nonunits = []

    E_fix = units + e_fix_nonunits  # all unit runners + specified non-units

    total_events = 0
    m1_events = 0
    isolated_events = []    # (eu, m, r_dep, covering_runners)
    covered_events = []

    for eu in units:
        if eu < 2:
            continue
        for m in range(1, eu):  # m = 1, ..., eu-1
            r_dep = compute_r_dep(eu, m, n)
            if r_dep is None:
                continue

            total_events += 1
            if m == 1:
                m1_events += 1
                # Always covered by e'=1 via Cond1 (s=1*1 mod eu = 1 = e')
                covered_events.append((eu, m, r_dep, [1], 'm1'))
                continue

            # m >= 2: check all other runners
            covering = []
            for ep in E_fix:
                if ep == eu:
                    continue
                # Check via Cond1/Cond2 (for unit ep)
                if gcd(ep, n) == 1:
                    fires, cond_num = covers_via_cond_with_n(ep, eu, m, n)
                    if fires:
                        covering.append((ep, f'Cond{cond_num}'))
                        continue
                # Also verify via bad set directly (should agree for units)
                if covers_via_bad_set(ep, eu, m, r_dep, n):
                    covering.append((ep, 'BadSet'))

            if covering:
                covered_events.append((eu, m, r_dep, covering, 'relay'))
            else:
                isolated_events.append((eu, m, r_dep))

    if verbose:
        print(f"\nn={n}, phi={phi(n)}, units={units}, nonunit_fix={e_fix_nonunits}")
        print(f"  Total z=0 events: {total_events}  (m=1: {m1_events}, m>=2: {total_events - m1_events})")
        print(f"  Isolated (no coverage): {len(isolated_events)}")
        print(f"  Covered: {len(covered_events) - m1_events}")
        if isolated_events:
            print(f"  Isolated events:")
            for eu, m, r_dep in isolated_events:
                print(f"    e_u={eu}, m={m}, r_dep={r_dep}")
        if not isolated_events:
            print(f"  *** ZERO ISOLATED EVENTS — Gap A counterexample candidate! ***")

    return {
        'n': n,
        'units': units,
        'nonunit_fix': e_fix_nonunits,
        'total': total_events,
        'm1_count': m1_events,
        'm2plus_count': total_events - m1_events,
        'isolated_count': len(isolated_events),
        'isolated_events': isolated_events,
        'covered_events': covered_events,
    }

# ============================================================
print("=" * 70)
print("PART 1: Pure unit relay — find cases with zero isolated events")
print("=" * 70)

zero_isolated = []
min_iso_by_n = {}

for n in range(4, 50):
    units = units_mod_n(n)
    if len(units) < 2:
        continue
    result = analyze_n(n, e_fix_nonunits=[], verbose=False)
    iso = result['isolated_count']
    m2 = result['m2plus_count']
    min_iso_by_n[n] = (iso, m2)
    if iso == 0:
        zero_isolated.append(n)
        print(f"n={n:3d}: ZERO isolated events! (m>=2 events: {m2})")
    else:
        frac = iso / m2 if m2 > 0 else 0
        print(f"n={n:3d}: isolated={iso:3d}/{m2:3d} = {frac:.3f}  phi={phi(n)}")

if zero_isolated:
    print(f"\n*** Found n with zero isolated events: {zero_isolated} ***")
else:
    print(f"\nNo n in [4,50) has zero isolated events. Gap A candidate confirmed non-trivial.")

# ============================================================
print("\n" + "=" * 70)
print("PART 2: Detailed anatomy of covered events — what fires Cond1 vs Cond2?")
print("=" * 70)

for n in [5, 6, 7, 8, 9, 10, 12, 13]:
    units = units_mod_n(n)
    result = analyze_n(n, verbose=False)

    cond1_count = sum(1 for eu, m, r_dep, cov, typ in result['covered_events']
                      if typ == 'relay' and any('Cond1' in c[1] for c in cov))
    cond2_count = sum(1 for eu, m, r_dep, cov, typ in result['covered_events']
                      if typ == 'relay' and any('Cond2' in c[1] for c in cov))

    print(f"\nn={n} (phi={phi(n)}, units={units}):")
    print(f"  m>=2 events: {result['m2plus_count']}")
    print(f"  Isolated: {result['isolated_count']}")
    print(f"  Covered by Cond1 only: {cond1_count}")
    print(f"  Covered by Cond2: {cond2_count}")

    # Show covered events detail for small n
    if n <= 8:
        print(f"  Covered events (m>=2):")
        for eu, m, r_dep, cov, typ in result['covered_events']:
            if typ == 'relay':
                print(f"    e_u={eu}, m={m}, r_dep={r_dep} <- {cov}")
        print(f"  Isolated events:")
        for eu, m, r_dep in result['isolated_events']:
            print(f"    e_u={eu}, m={m}, r_dep={r_dep}  [SAFE FIBRE]")

# ============================================================
print("\n" + "=" * 70)
print("PART 3: What triggers Cond2? Find all Cond2 events.")
print("=" * 70)

print("\nCond2 fires when: e' + e_u >= n AND s = e' + e_u - n")
print("This requires e' > n - e_u, i.e., e' is 'large' relative to n.")
print("\nCond2 events by n:\n")

for n in range(5, 25):
    units = units_mod_n(n)
    cond2_events = []
    for eu in units:
        if eu < 2:
            continue
        for m in range(2, eu):
            for ep in units:
                if ep == eu:
                    continue
                s = (ep * m) % eu
                if ep + eu >= n and s == (ep + eu - n):
                    r_dep = compute_r_dep(eu, m, n)
                    cond2_events.append((eu, m, ep, r_dep))

    if cond2_events:
        print(f"n={n}: {len(cond2_events)} Cond2 events: {cond2_events[:5]}{'...' if len(cond2_events)>5 else ''}")
    else:
        print(f"n={n}: 0 Cond2 events")

# ============================================================
print("\n" + "=" * 70)
print("PART 4: Tight cases — events with MINIMUM coverage count")
print("(closest to being isolated — only 1 covering runner)")
print("=" * 70)

for n in [6, 7, 8, 9, 10, 11, 12, 13, 15, 16, 18, 20]:
    units = units_mod_n(n)
    result = analyze_n(n, verbose=False)

    # Find covered events with exactly 1 covering runner (most fragile)
    fragile = [(eu, m, r_dep, cov) for eu, m, r_dep, cov, typ in result['covered_events']
               if typ == 'relay' and len(cov) == 1]

    if fragile:
        print(f"\nn={n}: {len(fragile)} fragile covered events (exactly 1 covering runner):")
        for eu, m, r_dep, cov in fragile[:5]:
            print(f"  e_u={eu}, m={m}, r_dep={r_dep}, covered_by={cov}")

# ============================================================
print("\n" + "=" * 70)
print("PART 5: Pattern of isolated events — arithmetic structure")
print("=" * 70)

print("\nFor each n, list the isolated (e_u, m, r_dep) and check for patterns:")

for n in [5, 6, 7, 8, 9, 10, 11, 12, 13]:
    result = analyze_n(n, verbose=False)
    units = units_mod_n(n)

    print(f"\nn={n}, units={units}:")
    if not result['isolated_events']:
        print("  (no isolated events)")
        continue

    for eu, m, r_dep in result['isolated_events']:
        inv_eu = modinv(eu, n)
        # Check: is m ≡ 1 mod (eu/gcd)? Is r_dep a unit or non-unit?
        g = gcd(m, eu)
        is_unit_rdep = gcd(r_dep, n) == 1 if r_dep != 0 else False
        print(f"  e_u={eu}, m={m}, r_dep={r_dep}  "
              f"[gcd(m,eu)={g}, r_dep_unit={is_unit_rdep}, "
              f"m/eu={m}/{eu}={m/eu:.4f}]")

# ============================================================
print("\n" + "=" * 70)
print("PART 6: Non-unit runner impact — do non-units kill remaining isolated events?")
print("=" * 70)

print("\nFor composite n, add non-unit runners to E_fix and recheck isolated count:")

for n in [6, 8, 9, 10, 12, 15]:
    nonunits = nonunits_mod_n(n)
    units = units_mod_n(n)

    # Pure unit E_fix
    r_pure = analyze_n(n, e_fix_nonunits=[], verbose=False)
    print(f"\nn={n}: nonunits={nonunits}")
    print(f"  Pure unit E_fix: isolated={r_pure['isolated_count']}/{r_pure['m2plus_count']}")

    # Add each non-unit individually
    for nu in nonunits:
        r_nu = analyze_n(n, e_fix_nonunits=[nu], verbose=False)
        # Which isolated events got covered by this non-unit?
        still_isolated = []
        newly_covered = []
        for eu, m, r_dep in r_pure['isolated_events']:
            if covers_via_bad_set(nu, eu, m, r_dep, n):
                newly_covered.append((eu, m, r_dep))
            else:
                still_isolated.append((eu, m, r_dep))
        if newly_covered:
            print(f"  +nonunit {nu}: covers {len(newly_covered)} prev-isolated: {newly_covered}")
            print(f"    -> new isolated={r_nu['isolated_count']}")
        else:
            print(f"  +nonunit {nu}: covers 0 prev-isolated -> isolated still={r_nu['isolated_count']}")

# ============================================================
print("\n" + "=" * 70)
print("PART 7: Large n scan — does isolated_count/m2plus_count stay bounded away from 0?")
print("=" * 70)

print("\nn, phi(n), isolated, m2plus, ratio, min_ratio_needed_for_Bsafe>=1")
print("-" * 70)

for n in range(4, 120):
    units = units_mod_n(n)
    if len(units) < 2:
        continue
    result = analyze_n(n, verbose=False)
    iso = result['isolated_count']
    m2 = result['m2plus_count']
    if m2 == 0:
        continue
    ratio = iso / m2
    # Mark prime vs composite
    is_prime = phi(n) == n - 1
    tag = 'P' if is_prime else 'C'

    if iso == 0:
        print(f"n={n:3d} [{tag}]: ZERO ISOLATED *** phi={phi(n):3d} m2={m2:4d}")
    elif ratio < 0.05:
        print(f"n={n:3d} [{tag}]: iso={iso:3d}/{m2:4d} = {ratio:.4f}  phi={phi(n):3d}  <-- LOW RATIO")
    # Always print small n and n with low ratio
    elif n <= 20 or ratio < 0.1:
        print(f"n={n:3d} [{tag}]: iso={iso:3d}/{m2:4d} = {ratio:.4f}  phi={phi(n):3d}")

# ============================================================
print("\n" + "=" * 70)
print("PART 8: Deep dive — what makes an event isolated?")
print("(Algebraic characterisation attempt)")
print("=" * 70)

print("""
For unit e_u and m>=2, r_dep = -(m-1)·e_u^{-1} mod n.
Event is isolated iff no e' in units covers it via Cond1/Cond2.

Cond1 fires for e' < e_u iff: e'·m ≡ e' (mod e_u) iff e'(m-1) ≡ 0 (mod e_u)
  iff e_u | e'(m-1)  iff e_u/gcd(e_u,e') | (m-1).
  So Cond1 fails for all e' < e_u iff: for all e' < e_u with gcd(e',n)=1,
  e_u/gcd(e_u,e') does NOT divide (m-1).

Cond2 fires for e' with e_u < e' and e' + e_u >= n iff: e'·m ≡ e'+e_u-n (mod e_u)
  iff e'·m ≡ e'-n+e_u (mod e_u)  iff e'(m-1) ≡ e_u-n (mod e_u) iff e'(m-1) ≡ -n (mod e_u).

For event (e_u, m) to be isolated:
  Cond1 fails: e_u/gcd(e_u,e') does NOT divide (m-1) for any unit e' < e_u.
  Cond2 fails: e'(m-1) ≢ -n (mod e_u) for any unit e' with e' > n-e_u.
""")

# Test the Cond1 algebraic characterisation
print("Verifying Cond1 algebraic form: Cond1 fires iff e_u/gcd(e_u,e') | (m-1)")
errors = 0
for n in range(5, 30):
    units = units_mod_n(n)
    for eu in units:
        if eu < 2:
            continue
        for m in range(2, eu):
            for ep in units:
                if ep >= eu:
                    continue
                s = (ep * m) % eu
                cond1_via_s = (s == ep)
                div_form = (eu // gcd(eu, ep)) % (m - 1 if m > 1 else 1) == 0 if m > 1 else True
                # m-1 divisible by e_u/gcd(e_u,e')
                divisor = eu // gcd(eu, ep)
                div_form2 = ((m - 1) % divisor == 0)
                if cond1_via_s != div_form2:
                    errors += 1
                    if errors <= 5:
                        print(f"  MISMATCH: n={n} e_u={eu} e'={ep} m={m}: s={s} e'={ep} cond1_s={cond1_via_s} div_form={div_form2} divisor={divisor}")
print(f"Algebraic Cond1 check: {errors} mismatches (expected 0)")

# ============================================================
print("\n" + "=" * 70)
print("PART 9: ISOLATION THEOREM CANDIDATE")
print("(Which (e_u, m) pairs are always isolated, regardless of n?)")
print("=" * 70)

print("\nFor prime e_u > n/2 (so all smaller units are < e_u < n - e_u or similar):")
print("Looking for e_u, m with: gcd(m-1, e_u) = e_u-1 or m-1 = e_u-1...")
print()

# Check: is (e_u = second-largest unit, m = e_u - 1) always isolated?
print("Checking: is (e_u = largest unit = n-1, m = n-2) always isolated?")
print("  r_dep = -(n-3)·(n-1)^{-1} mod n = -(n-3)·(-1) mod n = n-3 (since (n-1)^{-1} = -1 mod n)")
print("  So r_dep = n-3 for this event.\n")

for n in range(5, 40):
    eu = n - 1  # largest unit (n-1 is always a unit since gcd(n-1,n)=1)
    m = eu - 1  # = n - 2
    r_dep = compute_r_dep(eu, m, n)
    units = units_mod_n(n)

    if eu not in units:
        continue

    # Check all other units for Cond1/Cond2
    covering = []
    for ep in units:
        if ep == eu:
            continue
        fires, cnum = covers_via_cond_with_n(ep, eu, m, n)
        if fires:
            covering.append((ep, f'Cond{cnum}'))

    isolated = len(covering) == 0
    expected_rdep = (n - 3) % n
    print(f"  n={n:3d}: e_u={eu}, m={m}, r_dep={r_dep} (expected {expected_rdep}), "
          f"isolated={isolated}{'  <-- COVERED by '+str(covering) if not isolated else '  [CONFIRMED ISOLATED]'}")

print("\n\nChecking: (e_u = n-1, m = 2) event:")
print("  r_dep = -(1)·(n-1)^{-1} mod n = -(-1) mod n = 1")
for n in range(5, 30):
    eu = n - 1
    m = 2
    r_dep = compute_r_dep(eu, m, n)
    units = units_mod_n(n)
    if eu not in units or m >= eu:
        continue
    covering = []
    for ep in units:
        if ep == eu:
            continue
        fires, cnum = covers_via_cond_with_n(ep, eu, m, n)
        if fires:
            covering.append((ep, f'Cond{cnum}'))
    isolated = len(covering) == 0
    print(f"  n={n:3d}: e_u={eu}, m=2, r_dep={r_dep} (expected 1), "
          f"isolated={isolated}{'  COVERED='+str(covering) if not isolated else '  [ISOLATED]'}")

print("\n\nChecking: (e_u = second-largest unit, m = e_u-1):")
for n in range(7, 30):
    units = units_mod_n(n)
    if len(units) < 3:
        continue
    eu = sorted(units)[-2]  # second largest
    m = eu - 1
    if m < 2:
        continue
    r_dep = compute_r_dep(eu, m, n)
    covering = []
    for ep in units:
        if ep == eu:
            continue
        fires, cnum = covers_via_cond_with_n(ep, eu, m, n)
        if fires:
            covering.append((ep, f'Cond{cnum}'))
    isolated = len(covering) == 0
    print(f"  n={n:3d}: e_u={eu} (2nd-largest), m={m}, r_dep={r_dep}, "
          f"isolated={isolated}{'  COVERED='+str(covering[:2]) if not isolated else ''}")
