"""
z0s_audit_v1.py — Z0S Gap A Numerical Audit
=============================================
Investigates Gap A: at each z=0 event of a unit runner eᵤ at floor m ≥ 2,
does the departing residue r_dep = -(m-1)·eᵤ⁻¹ mod n get "covered" by
any other runner in E_non?

Key algebraic criterion (from the plan):
  Runner e' covers r_dep of eᵤ at event m iff (eᵤ / gcd(eᵤ, e')) | (m-1).
  In particular, for pairwise-coprime unit runners: gcd(eᵤ, e') = 1 for all
  pairs, so the criterion becomes eᵤ | (m-1), which fails for 1 ≤ m ≤ eᵤ-1.
  => Gap A is analytically CLOSED for pairwise-coprime runner sets.

Outputs for each n ∈ {6, 8, 9, 10, 12}:
  1. List of all unit pairs (eᵤ, e') with gcd > 1 (candidates for interference).
  2. For each unit eᵤ, for each z=0 event m (1 ≤ m ≤ eᵤ-1):
       - r_dep = -(m-1)·eᵤ⁻¹ mod n
       - For each other runner e' in E_non, check if e' covers r_dep at event m.
       - Record: is r_dep "isolated" (no other runner covers it)?
  3. B_safe lower bound: count of z=0 events with isolated r_dep.
  4. Compare B_safe_min to φ(n)(n-2)/2.

The "U-FORCE" scenario (all φ(n) units in E_non) is the relevant case.
"""

from math import gcd
from functools import reduce
from itertools import combinations

def modinv(a, n):
    """Extended Euclidean modular inverse; raises ValueError if gcd(a,n)!=1."""
    g, x, _ = extended_gcd(a % n, n)
    if g != 1:
        raise ValueError(f"No inverse: gcd({a},{n})={g}")
    return x % n

def extended_gcd(a, b):
    if a == 0:
        return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def phi(n):
    """Euler's totient function."""
    result = n
    p = 2
    temp = n
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
    """Return list of units in {1,...,n-1}."""
    return [e for e in range(1, n) if gcd(e, n) == 1]

def bad_set(e, t, n):
    """
    bad(e, t, n) = Sol(e, -t, n) ∪ Sol(e, -(t+1), n)
    Sol(e, j, n) = {r : e·r ≡ j (mod n)}
    """
    g = gcd(e, n)
    result = set()
    for j in [-t, -(t + 1)]:
        j_mod = j % n
        if j_mod % g == 0:
            # Solutions: r₀ = (j/g)·(e/g)⁻¹ mod (n/g), then r = r₀ + k·(n/g)
            try:
                r0 = (j_mod // g) * modinv(e // g, n // g) % (n // g)
                for k in range(g):
                    result.add((r0 + k * (n // g)) % n)
            except ValueError:
                pass
    return result

def covers_residue(e_prime, t_ep, r, n):
    """Does runner e' at floor state t_ep have r in its bad set?"""
    return r in bad_set(e_prime, t_ep, n)

def floor_state_at_z0_event(e_u, m, e_prime, n):
    """
    At the m-th z=0 event of unit runner eᵤ, what floor state is e' at?
    The m-th z=0 event of eᵤ occurs at fibre b such that eᵤ·b/L crosses m.
    In the normalised model: the floor state of e' at the fibre of eᵤ's m-th event
    is ⌊e'·(m·L/eᵤ)/L⌋ = ⌊e'·m/eᵤ⌋.
    Note: this is the "synchronised" floor state in the period model.
    """
    return (e_prime * m) // e_u

def z0s_audit_for_n(n, verbose=True):
    """
    Full Z0S Gap-A audit for a given n.
    Returns:
      - b_safe_min: minimum B_safe from z=0 events across all runner configs
      - theoretical_bound: φ(n)(n-2)/2
      - gap_a_closed: True if ALL z=0 events have isolated departing residues
    """
    units = units_mod_n(n)
    phi_n = phi(n)
    theoretical_bound = phi_n * (n - 2) // 2  # integer division ok since one of phi, n-2 is even

    if verbose:
        print(f"\n{'='*60}")
        print(f"n = {n}, φ(n) = {phi_n}, units = {units}")
        print(f"Theoretical bound Z0S.3: φ(n)(n-2)/2 = {phi_n}·{n-2}/2 = {phi_n*(n-2)/2:.1f}")
        print(f"(integer floor: {theoretical_bound})")
        print()

    # U-FORCE scenario: all φ(n) units are in E_non
    E_non = units[:]  # all units active

    # Check pairwise coprimality
    pairwise_coprime = all(gcd(u, v) == 1 for u, v in combinations(units, 2))
    if verbose:
        print(f"Unit pairs with gcd > 1:")
        non_coprime_pairs = [(u, v) for u, v in combinations(units, 2) if gcd(u, v) > 1]
        if non_coprime_pairs:
            for u, v in non_coprime_pairs:
                print(f"  gcd({u},{v}) = {gcd(u,v)}")
            print(f"  => NOT pairwise coprime. Gap A potentially OPEN.")
        else:
            print(f"  None. All unit pairs coprime. Gap A CLOSED for this n.")
        print()

    # For each unit eᵤ, analyse each z=0 event m = 1,...,eᵤ-1
    total_z0_events = 0
    isolated_events = 0
    covered_events = []

    for e_u in units:
        if e_u == 1:
            continue  # runner 1 has no z=0 events (eᵤ-1 = 0)
        inv_eu = modinv(e_u, n)
        for m in range(1, e_u):
            # Departing residue: r_dep = -(m-1)·eᵤ⁻¹ mod n
            r_dep = (-(m - 1) * inv_eu) % n
            total_z0_events += 1

            # Check if r_dep is isolated: no other runner e' in E_non covers it
            covered_by = []
            for e_prime in E_non:
                if e_prime == e_u:
                    continue
                # Floor state of e' at eᵤ's m-th z=0 event
                t_ep = floor_state_at_z0_event(e_u, m, e_prime, n)
                if covers_residue(e_prime, t_ep, r_dep, n):
                    covered_by.append(e_prime)

            # Algebraic criterion check: e' covers r_dep iff (eᵤ/gcd(eᵤ,e')) | (m-1)
            alg_criterion_covered = []
            for e_prime in E_non:
                if e_prime == e_u:
                    continue
                g = gcd(e_u, e_prime)
                ratio = e_u // g
                if ratio > 0 and (m - 1) % ratio == 0:
                    alg_criterion_covered.append(e_prime)

            is_isolated = (len(covered_by) == 0)
            if is_isolated:
                isolated_events += 1
            else:
                covered_events.append({
                    'e_u': e_u, 'm': m, 'r_dep': r_dep,
                    'covered_by': covered_by,
                    'alg_covered': alg_criterion_covered
                })

            if verbose and not is_isolated:
                print(f"  [COVERED] eᵤ={e_u}, m={m}: r_dep={r_dep} covered by {covered_by}")
                print(f"            Alg criterion says covered by: {alg_criterion_covered}")
                # Consistency check
                if set(covered_by) != set(alg_criterion_covered):
                    print(f"  [WARNING] Discrepancy between direct check and alg criterion!")

    if verbose:
        print(f"Z=0 events analysis:")
        print(f"  Total z=0 events (eᵤ≥2 unit runners): {total_z0_events}")
        print(f"  Expected: φ(n)(n-2)/2 = {phi_n*(n-2)//2}")  # sum of (eᵤ-1) for units ≥ 2
        print(f"  Isolated (no coverage): {isolated_events}")
        print(f"  Covered (Gap A at risk): {len(covered_events)}")

        if covered_events:
            print(f"\n  Summary of covered events:")
            for ev in covered_events:
                print(f"    eᵤ={ev['e_u']}, m={ev['m']}: r_dep={ev['r_dep']}, "
                      f"covered_by={ev['covered_by']}")
        else:
            print(f"\n  No covered events — all z=0 events produce SAFE fibres!")
            print(f"  Gap A is effectively CLOSED for n={n} in the U-FORCE scenario.")

        print(f"\n  B_safe (z=0 events only) ≥ {isolated_events}")
        print(f"  Theoretical bound φ(n)(n-2)/2 = {phi_n*(n-2)/2:.1f}")
        bound_int = phi_n * (n - 2) // 2
        if isolated_events >= bound_int:
            print(f"  ✓ B_safe ≥ φ(n)(n-2)/2 CONFIRMED")
        else:
            print(f"  ✗ B_safe < φ(n)(n-2)/2 — THEOREM 8.3 WOULD BE VIOLATED if these gaps are real")

    gap_a_closed = (len(covered_events) == 0)
    return {
        'n': n,
        'phi_n': phi_n,
        'units': units,
        'pairwise_coprime': pairwise_coprime,
        'total_z0_events': total_z0_events,
        'isolated_events': isolated_events,
        'covered_events': covered_events,
        'gap_a_closed_numerically': gap_a_closed,
        'theoretical_bound': theoretical_bound,
    }

def verify_algebraic_criterion(n_list=None, verbose=True):
    """
    Verify the algebraic criterion:
      Runner e' covers r_dep of eᵤ at event m iff (eᵤ/gcd(eᵤ,e')) | (m-1).
    Compare direct computation vs criterion for all triples (eᵤ, e', m).
    """
    if n_list is None:
        n_list = [6, 8, 9, 10, 12]

    if verbose:
        print("\n" + "="*60)
        print("ALGEBRAIC CRITERION VERIFICATION")
        print("Claim: e' covers r_dep(eᵤ, m) iff (eᵤ/gcd(eᵤ,e')) | (m-1)")
        print("="*60)

    total_checks = 0
    discrepancies = 0

    for n in n_list:
        units = units_mod_n(n)
        for e_u in units:
            if e_u == 1:
                continue
            inv_eu = modinv(e_u, n)
            for m in range(1, e_u):
                r_dep = (-(m - 1) * inv_eu) % n
                for e_prime in units:
                    if e_prime == e_u:
                        continue

                    # Direct check
                    t_ep = floor_state_at_z0_event(e_u, m, e_prime, n)
                    direct = covers_residue(e_prime, t_ep, r_dep, n)

                    # Algebraic criterion
                    g = gcd(e_u, e_prime)
                    ratio = e_u // g
                    alg = ((m - 1) % ratio == 0)

                    total_checks += 1
                    if direct != alg:
                        discrepancies += 1
                        if verbose:
                            print(f"  DISCREPANCY: n={n}, eᵤ={e_u}, e'={e_prime}, m={m}")
                            print(f"    r_dep={r_dep}, t_ep={t_ep}")
                            print(f"    direct={direct}, alg_criterion={alg}")
                            print(f"    gcd={g}, ratio={ratio}, (m-1)%ratio={(m-1)%ratio}")

    if verbose:
        print(f"\nTotal checks: {total_checks}")
        print(f"Discrepancies: {discrepancies}")
        if discrepancies == 0:
            print("✓ Algebraic criterion VERIFIED for all checked cases.")
        else:
            print(f"✗ Algebraic criterion has {discrepancies} failures — needs investigation.")

    return discrepancies == 0


def relay_invariant_audit(n_list=None, verbose=True):
    """
    For each n, check whether covered z=0 events still produce safe fibres
    via an alternative mechanism (relay invariant): even when r_dep is "covered"
    by some e', is there still an uncovered residue in miss(0) at that fibre?

    This tests whether Theorem 8.3's conclusion (B_safe ≥ bound) holds even
    when individual z=0 events lose their isolation.
    """
    if n_list is None:
        n_list = [6, 8, 9, 10, 12]

    if verbose:
        print("\n" + "="*60)
        print("RELAY INVARIANT AUDIT")
        print("For covered z=0 events: is there still a missing residue?")
        print("="*60)

    for n in n_list:
        units = units_mod_n(n)
        E_non = units[:]

        if verbose:
            print(f"\nn = {n}")

        all_safe = True
        for e_u in units:
            if e_u == 1:
                continue
            inv_eu = modinv(e_u, n)
            for m in range(1, e_u):
                r_dep = (-(m - 1) * inv_eu) % n
                t_ep_map = {e: floor_state_at_z0_event(e_u, m, e, n) for e in E_non if e != e_u}

                # Union of all bad sets at this floor state
                union_bad = set()
                for e in E_non:
                    if e == e_u:
                        # eᵤ itself: at its z=0 event, its bad set transitions.
                        # The "departing" side: bad(eᵤ, m-1, n) → bad(eᵤ, m, n).
                        # At the z=0 event fibre, both states are relevant;
                        # conservatively include both.
                        union_bad |= bad_set(e_u, m - 1, n)
                        union_bad |= bad_set(e_u, m, n)
                    else:
                        t = t_ep_map[e]
                        union_bad |= bad_set(e, t, n)

                miss = set(range(n)) - union_bad
                if not miss:
                    all_safe = False
                    if verbose:
                        print(f"  [UNSAFE] eᵤ={e_u}, m={m}: union_bad=Z_{n}, no safe residue!")
                        print(f"    t_ep_map = {t_ep_map}")
                else:
                    pass  # fibre is safe

        if all_safe:
            if verbose:
                print(f"  ✓ All z=0 event fibres have ≥1 uncovered residue for n={n}")


def main():
    print("Z0S GAP-A NUMERICAL AUDIT v1.0")
    print("="*60)
    print("Testing: do z=0 events produce safe fibres? (Gap A)")
    print("U-FORCE scenario: all φ(n) units active in E_non.")
    print()

    n_list = [6, 8, 9, 10, 12]
    results = {}

    # Part 1: Algebraic criterion verification
    print("PART 1: Verifying algebraic criterion for coverage")
    crit_ok = verify_algebraic_criterion(n_list, verbose=True)

    # Part 2: Per-n Z0S audit
    print("\nPART 2: Per-n Z0S event audit")
    for n in n_list:
        r = z0s_audit_for_n(n, verbose=True)
        results[n] = r

    # Part 3: Relay invariant (full bad-set union at each z=0 event)
    print("\nPART 3: Relay invariant — full bad-set union at z=0 events")
    relay_invariant_audit(n_list, verbose=True)

    # Summary table
    print("\n" + "="*60)
    print("SUMMARY TABLE")
    print(f"{'n':>4} | {'φ(n)':>5} | {'Coprime?':>8} | {'z=0 events':>10} | "
          f"{'Isolated':>8} | {'Covered':>7} | {'Bound':>6} | {'Status'}")
    print("-"*80)
    for n in n_list:
        r = results[n]
        bound = r['phi_n'] * (n - 2) // 2
        status = "CLOSED" if r['gap_a_closed_numerically'] else f"OPEN ({len(r['covered_events'])} events)"
        coprime_str = "Yes" if r['pairwise_coprime'] else "No"
        print(f"{n:>4} | {r['phi_n']:>5} | {coprime_str:>8} | {r['total_z0_events']:>10} | "
              f"{r['isolated_events']:>8} | {len(r['covered_events']):>7} | {bound:>6} | {status}")

    print("\nNotes:")
    print("  'Isolated' = z=0 event where r_dep is not in any other runner's bad set.")
    print("  'Covered'  = z=0 event where some other runner covers r_dep (Gap A risk).")
    print("  'Bound'    = φ(n)(n-2)/2 (Theorem 8.3 lower bound on B_safe).")
    print("  Gap A is 'CLOSED' for n iff all z=0 events are isolated.")
    print()
    print("  Pairwise-coprime units => algebraic criterion guarantees isolation for m≥2.")
    print("  Non-coprime pairs => must check case-by-case (done above).")


if __name__ == "__main__":
    main()
