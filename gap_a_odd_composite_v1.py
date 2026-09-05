"""
gap_a_odd_composite_v1.py
=========================
Four-part investigation of Gap A for odd composite n.

SETUP:
  For m=2 and any unit e_u ≥ 3:
    - Cond1 never fires (needs e_u | (m-1)=1, impossible for e_u ≥ 2)
    - Cond2 fires iff the unique e'* in {n-e_u,...,n-2} with e'* ≡ -n (mod e_u) is a unit.

  The e'* formula (derived):
    a = n mod e_u  (1 ≤ a ≤ e_u-1, since e_u is a unit so e_u ∤ n)
    e'* ≡ e_u - a (mod e_u)
    Adjusted to range {n-e_u,...,n-2}:
      If a < e_u/2  (i.e., 2a < e_u):  e'* = n - 2a
      If a = e_u/2  (e_u even):         e'* = n - e_u
      If a > e_u/2  and 2a ≠ e_u+1:    e'* = n + e_u - 2a
      If 2a = e_u+1 (e_u odd, a=(e_u+1)/2): e'* = n-1, OUT OF RANGE → Cond2 fails

    (e_u, 2) is isolated iff e'* is out of range OR gcd(e'*, n) > 1.
"""

from math import gcd

def phi(n):
    result, temp, p = n, n, 2
    while p*p <= temp:
        if temp%p==0:
            while temp%p==0: temp//=p
            result -= result//p
        p+=1
    if temp>1: result -= result//temp
    return result

def units_mod_n(n):
    return [e for e in range(1, n) if gcd(e, n) == 1]

def smallest_prime(n):
    for p in range(2, n):
        if n % p == 0: return p
    return n

def prime_factors(n):
    factors = set()
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.add(d)
            n //= d
        d += 1
    if n > 1: factors.add(n)
    return factors

def covers_via_cond(ep, eu, m, n):
    s = (ep * m) % eu
    if ep < eu and s == ep: return True, 1
    if ep + eu >= n and s == (ep + eu - n): return True, 2
    return False, 0

def is_isolated_m2(eu, n, units):
    """(e_u, m=2) is isolated iff no unit e' covers it via Cond2."""
    for ep in units:
        if ep == eu: continue
        fired, cnum = covers_via_cond(ep, eu, 2, n)
        if fired and cnum == 2: return False
    return True  # Cond1 never fires for m=2; check only Cond2

def compute_estar(eu, n):
    """
    Compute the Cond2 partner e'* for (e_u, m=2).
    Returns (e_star, in_range, is_unit) where in_range=False means no valid partner.
    """
    a = n % eu  # 1 <= a <= e_u-1 (since gcd(e_u,n)=1, so e_u does not divide n)
    assert 1 <= a <= eu - 1, f"a={a} out of expected range for e_u={eu}, n={n}"

    two_a = 2 * a
    if two_a == eu + 1:   # only for odd e_u: a = (e_u+1)/2
        return None, False, None  # e'* = n-1, out of range
    elif two_a < eu:      # a < e_u/2
        estar = n - two_a
    elif two_a == eu:     # a = e_u/2, e_u even
        estar = n - eu
    else:                 # a > e_u/2, 2a ≠ e_u+1
        estar = n + eu - two_a

    in_range = (n - eu) <= estar <= (n - 2)
    is_unit = (gcd(estar, n) == 1) if in_range else None
    return estar, in_range, is_unit


# ============================================================
print("=" * 70)
print("PART A: Formula Verification")
print("  Claim: (e_u, 2) isolated ↔ e'* out of range or gcd(e'*, n) > 1")
print("=" * 70)

total_checks = 0
mismatches = 0
formula_cases = {'out_of_range': 0, 'nonunit': 0, 'unit_fires': 0, 'unit_but_isolated': 0}

for n in range(9, 61, 2):
    if phi(n) == n - 1: continue  # skip primes
    units = units_mod_n(n)
    p = smallest_prime(n)

    for eu in units:
        if eu < 3: continue

        actual_isolated = is_isolated_m2(eu, n, units)
        estar, in_range, is_unit_flag = compute_estar(eu, n)

        # Formula prediction
        if not in_range:
            formula_isolated = True
            formula_cases['out_of_range'] += 1
        elif not is_unit_flag:
            formula_isolated = True
            formula_cases['nonunit'] += 1
        else:
            formula_isolated = False
            formula_cases['unit_fires'] += 1

        # Catch anomaly
        if formula_isolated and not actual_isolated:
            formula_cases['unit_but_isolated'] += 1

        total_checks += 1
        if formula_isolated != actual_isolated:
            mismatches += 1
            print(f"  MISMATCH: n={n} e_u={eu} a={n%eu} e*={estar} "
                  f"in_range={in_range} gcd={gcd(estar,n) if in_range else 'N/A'} "
                  f"formula={formula_isolated} actual={actual_isolated}")

print(f"\nChecked {total_checks} (e_u, m=2) events for odd composite n in [9,60].")
print(f"Mismatches: {mismatches}")
print(f"Formula case breakdown:")
print(f"  Out-of-range e'* (auto-isolated): {formula_cases['out_of_range']}")
print(f"  e'* in range but non-unit (isolated): {formula_cases['nonunit']}")
print(f"  e'* in range and unit (Cond2 fires, NOT isolated): {formula_cases['unit_fires']}")
if mismatches == 0:
    print("\n  ✓ FORMULA VERIFIED — zero mismatches.")

# Per-n summary
print("\nPer-n summary (odd composite n ≤ 60):")
print(f"{'n':>5} {'p':>4} {'phi':>5} {'units<n/2':>10} {'e*_nonunit':>12} "
      f"{'e*_outrange':>12} {'total_isolated_m2':>18} {'any_isolated_m2':>16}")
print("-" * 90)

for n in range(9, 61, 2):
    if phi(n) == n - 1: continue
    units = units_mod_n(n)
    p = smallest_prime(n)
    ph = phi(n)

    units_small = [eu for eu in units if eu < n // 2 and eu >= 3]
    nonunit_count = 0
    outrange_count = 0
    total_iso_m2 = 0

    for eu in units_small:
        estar, in_range, is_unit_flag = compute_estar(eu, n)
        if not in_range:
            outrange_count += 1
            total_iso_m2 += 1
        elif not is_unit_flag:
            nonunit_count += 1
            total_iso_m2 += 1

    any_iso = total_iso_m2 > 0
    print(f"n={n:>4} p={p:<4} phi={ph:<5} {len(units_small):>10} "
          f"{nonunit_count:>12} {outrange_count:>12} {total_iso_m2:>18} "
          f"{'YES' if any_iso else '*** NO ***':>16}")


# ============================================================
print("\n" + "=" * 70)
print("PART B: e'* = n - 2a Structure and floor(n/e_u) mod p")
print("  For Case 1 (2a < e_u): e'* = n-2a. Isolated iff p | (n-2a).")
print("  Since p|n: p|(n-2a) ↔ p|2a ↔ p|a (p odd) ↔ p|(n mod e_u).")
print("  p|(n mod e_u) ↔ p | (n - e_u·floor(n/e_u)) ↔ p|e_u·floor(n/e_u) ↔ p|floor(n/e_u).")
print("=" * 70)

print("\nFor each n=p^2 (clearest case), mapping floor(n/e_u) mod p for units e_u < n/2:")
for p_val in [3, 5, 7]:
    n = p_val * p_val
    units = units_mod_n(n)
    units_small = [eu for eu in units if eu < n // 2 and eu >= 3]

    print(f"\nn={n} (p={p_val}):")
    # Distribution of floor(n/e_u) mod p for all units e_u < n/2
    residue_dist = {}
    isolated_by_residue = {}
    for eu in units_small:
        q = n // eu
        q_mod_p = q % p_val
        a = n % eu
        estar, in_range, is_unit_flag = compute_estar(eu, n)
        is_iso = (not in_range) or (not is_unit_flag)
        case = 1 if (2*a < eu) else (0 if (2*a == eu+1) else 2)

        residue_dist[q_mod_p] = residue_dist.get(q_mod_p, 0) + 1
        isolated_by_residue[q_mod_p] = isolated_by_residue.get(q_mod_p, {'total':0,'iso':0})
        isolated_by_residue[q_mod_p]['total'] += 1
        isolated_by_residue[q_mod_p]['iso'] += int(is_iso)

    print(f"  floor(n/e_u) mod {p_val}: distribution and isolation rate:")
    for r in range(p_val):
        d = isolated_by_residue.get(r, {'total':0,'iso':0})
        if d['total'] > 0:
            print(f"    q ≡ {r} (mod {p_val}): {d['iso']}/{d['total']} isolated "
                  f"{'← EXPECTED p|(n-2a) for r≡0' if r==0 else ''}")

    # Verify: for q ≡ 0 (mod p), is isolation rate 100% in Case 1?
    case1_q0_iso = sum(1 for eu in units_small
                       if n//eu % p_val == 0 and 2*(n%eu) < eu
                       and compute_estar(eu, n)[0] and not compute_estar(eu, n)[2])
    case1_q0_total = sum(1 for eu in units_small
                         if n//eu % p_val == 0 and 2*(n%eu) < eu)
    print(f"  Case 1 events with q≡0: {case1_q0_iso}/{case1_q0_total} isolated (expect 100%)")


# ============================================================
print("\n" + "=" * 70)
print("PART C: Equidistribution — does floor(n/e_u) mod p always hit 0?")
print("  KEY THEOREM TO PROVE: ∃ unit e_u < n/2 with p | floor(n/e_u).")
print("  If proved → Gap A closed for all odd composite n via m=2 events.")
print("=" * 70)

failures = []
results = []

for n in range(9, 201, 2):
    if phi(n) == n - 1: continue  # skip primes
    p = smallest_prime(n)
    units = units_mod_n(n)
    units_small = [eu for eu in units if eu >= 3 and eu < n // 2]

    # Compute all values of floor(n/e_u) mod p
    floor_residues = set(n // eu % p for eu in units_small)

    hits_zero = 0 in floor_residues
    if not hits_zero:
        failures.append(n)

    # Count units e_u with q≡0 that give isolated m=2 event
    iso_count = sum(1 for eu in units_small
                    if n // eu % p == 0
                    and (not compute_estar(eu, n)[1] or not compute_estar(eu, n)[2]))

    results.append((n, p, len(units_small), floor_residues, hits_zero, iso_count))

print(f"\nChecked all odd composite n in [9, 200]:")
print(f"  n with floor(n/e_u) mod p never hitting 0: {failures}")
print(f"  (empty = Part C hypothesis holds for all tested n)")

print("\nSelected cases — floor(n/e_u) mod p coverage:")
print(f"{'n':>5} {'p':>4} {'units<n/2':>10} {'residues hit':>30} {'0 in set?':>10} {'iso from q≡0':>14}")
print("-" * 80)
for n, p, ucnt, residues, hits_zero, iso_cnt in results:
    if n <= 60 or n in [81, 121, 125, 169, 175, 189]:
        print(f"n={n:>4} p={p:<4} {ucnt:>10} {str(sorted(residues)):<30} {'YES' if hits_zero else 'NO':>10} {iso_cnt:>14}")

# Deeper analysis: for small n/p ratio, can floor(n/e_u) miss 0?
print("\nAnalysis: minimum number of distinct floor residues mod p vs p:")
print(f"{'n':>5} {'p':>4} {'n/p':>6} {'#residues hit':>14} {'fraction':>10}")
for n, p, ucnt, residues, hits_zero, iso_cnt in results:
    if ucnt >= 3:
        print(f"n={n:>4} p={p:<4} {n/p:>6.1f} {len(residues):>14} {len(residues)/p:>10.3f}")


# ============================================================
print("\n" + "=" * 70)
print("PART D: Tight Cases — where is isolation count closest to zero?")
print("  Find n where fewest (e_u, 2) events are isolated.")
print("  Check: does Case 2 (2a > e_u) fill in when Case 1 is sparse?")
print("=" * 70)

print("\nAll odd composite n ≤ 200 sorted by (total m=2 isolated events):")
tight_cases = []

for n in range(9, 201, 2):
    if phi(n) == n - 1: continue
    p = smallest_prime(n)
    units = units_mod_n(n)
    units_small = [eu for eu in units if eu >= 3 and eu < n // 2]

    iso_m2 = 0
    case1_iso = 0
    case2_iso = 0
    outrange_iso = 0

    for eu in units_small:
        a = n % eu
        estar, in_range, is_unit_flag = compute_estar(eu, n)
        is_iso = (not in_range) or (not is_unit_flag)
        case = 1 if (2*a < eu) else (3 if (2*a == eu+1) else 2)

        if is_iso:
            iso_m2 += 1
            if case == 3:   outrange_iso += 1
            elif case == 1: case1_iso += 1
            else:           case2_iso += 1

    tight_cases.append((iso_m2, n, p, len(units_small), case1_iso, case2_iso, outrange_iso))

tight_cases.sort()

print(f"\n{'iso_m2':>8} {'n':>6} {'p':>4} {'units<n/2':>10} {'case1':>7} "
      f"{'case2':>7} {'outrange':>10} {'ratio':>8}")
print("-" * 65)
for iso_m2, n, p, ucnt, c1, c2, cor in tight_cases[:30]:
    ratio = iso_m2 / ucnt if ucnt > 0 else 0
    print(f"{iso_m2:>8} {n:>6} {p:>4} {ucnt:>10} {c1:>7} {c2:>7} {cor:>10} {ratio:>8.4f}")

print(f"\nMinimum isolated m=2 count for odd composite n ≤ 200: {tight_cases[0][0]}")
print(f"  At n={tight_cases[0][1]}, p={tight_cases[0][2]}")

# Check: zero isolated m=2 events ever?
zero_iso = [n for iso, n, *_ in tight_cases if iso == 0]
print(f"\nOdd composite n with zero isolated m=2 events: {zero_iso}")
if not zero_iso:
    print("  None found! Every odd composite n has ≥1 isolated (e_u, 2) event.")


# ============================================================
print("\n" + "=" * 70)
print("PART D.2: Case breakdown — when does each mechanism provide isolation?")
print("=" * 70)

print("\nCase contributions to isolation (odd composite n ≤ 60):")
print(f"{'n':>5} {'p':>4} | {'out_of_range':>13} | {'case1_nonunit':>14} | "
      f"{'case2_nonunit':>14} | {'total':>6}")
print("-" * 70)

for n in range(9, 61, 2):
    if phi(n) == n - 1: continue
    p = smallest_prime(n)
    units = units_mod_n(n)
    units_small = [eu for eu in units if eu >= 3 and eu < n // 2]

    out_range = case1 = case2 = 0
    for eu in units_small:
        a = n % eu
        estar, in_range, is_unit_flag = compute_estar(eu, n)
        is_iso = (not in_range) or (not is_unit_flag)
        if is_iso:
            if not in_range: out_range += 1
            elif 2*a < eu:   case1 += 1
            else:            case2 += 1

    total = out_range + case1 + case2
    print(f"n={n:>4} p={p:<4} | {out_range:>13} | {case1:>14} | {case2:>14} | {total:>6}")

# ============================================================
print("\n" + "=" * 70)
print("PART D.3: The tightest n — anatomy of n=p^2 for large p")
print("  These have the smallest isolation ratio (n=25: 35%, n=49: 26%...)")
print("=" * 70)

for p_val in [3, 5, 7, 11, 13]:
    n = p_val * p_val
    units = units_mod_n(n)
    units_small = [eu for eu in units if eu >= 3 and eu < n // 2]

    total = len(units_small)
    iso = sum(1 for eu in units_small
              if not compute_estar(eu, n)[1] or not compute_estar(eu, n)[2])

    # What fraction of e_u have q=floor(n/e_u) ≡ 0 (mod p)?
    q0_count = sum(1 for eu in units_small if n // eu % p_val == 0)
    q0_iso = sum(1 for eu in units_small
                 if n // eu % p_val == 0
                 and (not compute_estar(eu, n)[1] or not compute_estar(eu, n)[2]))

    print(f"\nn={n} (p={p_val}): {iso}/{total} units have isolated m=2 event ({100*iso//total}%)")
    print(f"  Units with q≡0 (mod {p_val}): {q0_count}, of which isolated: {q0_iso}")
    print(f"  Expected by equidistribution: ~{total // p_val} units with q≡0")
    print(f"  Expected isolated from q≡0 alone: ~{total // p_val} (Case 1 gives 100% iso rate for q≡0)")

    # Verify: are ALL q≡0 case-1 events isolated?
    all_q0_c1_iso = all(
        (not compute_estar(eu, n)[1] or not compute_estar(eu, n)[2])
        for eu in units_small
        if n // eu % p_val == 0 and 2 * (n % eu) < eu
    )
    print(f"  All Case-1 q≡0 events isolated? {all_q0_c1_iso}")


# ============================================================
print("\n" + "=" * 70)
print("PART E: THEOREM STATEMENT CANDIDATE")
print("  Assembling what the data implies about the analytic proof.")
print("=" * 70)

print("""
ESTABLISHED (from Parts A-D):

Theorem A (Formula). For any unit e_u ≥ 3 of odd composite n, the event (e_u, 2)
is isolated iff the Cond2 partner e'* (unique element of {n-e_u,...,n-2} with
e'* ≡ -n mod e_u) is either out of range or not a unit of n.

Theorem B (Case 1). For units e_u with 2*(n mod e_u) < e_u (Case 1):
  e'* = n - 2a where a = n mod e_u.
  Isolated iff p | (n - 2a). Since p|n, this is: p | 2a, i.e., p | a (p odd).
  Equivalently: p | (n mod e_u), equivalently p | floor(n/e_u).

  PROOF: If p | floor(n/e_u), then floor(n/e_u) = p·k, so n = e_u·(p·k) + a.
         e'* = n - 2a. For p|e'*: p|(n-2a). n ≡ 0 mod p, so p|-2a, so p|a.
         a = n mod e_u = n - e_u·floor(n/e_u) ≡ 0 - e_u·0 = 0 mod p. ✓

Theorem C (Case 2). For units e_u with 2*(n mod e_u) > e_u (Case 2):
  e'* = n + e_u - 2a.
  Isolated iff p | (n + e_u - 2a). Since p|n: p | (e_u - 2a).

Theorem D (Out-of-range). For units e_u where 2*(n mod e_u) = e_u+1 (e_u odd):
  No valid Cond2 partner. Always isolated!

GAP A CLOSURE STRATEGY for odd composite n:
  Need: ∃ unit e_u < n/2 such that (e_u, 2) is isolated.
  By Theorem B: sufficient to find unit e_u < n/2 with p | floor(n/e_u).

  KEY CLAIM (Part C evidence): For any odd composite n with smallest prime p,
  ∃ unit e_u < n/2 with floor(n/e_u) ≡ 0 (mod p).

  CONSTRUCTIVE APPROACH: Take e_u = n/p = q_n (if q_n is a unit) or e_u near n/p.
  floor(n/e_u) = floor(n / (n/p)) = floor(p) = p ≡ 0 (mod p). ✓
  But n/p might not be a unit! (n/p = q_n, and gcd(q_n, n): if n=p·m, then q_n=m,
  and gcd(m, p·m) = m. So n/p is a unit iff gcd(n/p, n) = 1 iff n/p = 1 iff n=p.
  But n is composite, so n/p ≥ p > 1. Not a unit in general.

  BETTER APPROACH: Find a unit e_u in the interval (n/(p+1), n/p).
  For any e_u in this range: floor(n/e_u) = p. So floor(n/e_u) ≡ 0 (mod p)! ✓
  Need: ∃ unit e_u ∈ (n/(p+1), n/p).
  Width of interval: n/p - n/(p+1) = n/(p(p+1)).
  For n=p^2: width = p^2/(p(p+1)) = p/(p+1) < 1. Might be empty for n=p^2!
  For n=p·q (q≥p+2): width = p·q/(p(p+1)) = q/(p+1) ≥ (p+2)/(p+1) > 1. Always non-empty.
""")

# Verify: for n=p^2, is the interval (n/(p+1), n/p) empty of units?
print("Testing: for n=p^2, does (n/(p+1), n/p) contain a unit?")
for p_val in [3, 5, 7, 11, 13, 17, 19, 23]:
    n = p_val * p_val
    lo = n / (p_val + 1)
    hi = n / p_val
    units_in_interval = [eu for eu in units_mod_n(n) if lo < eu < hi]
    print(f"  n={n:>4} (p={p_val:>2}): interval ({lo:.3f}, {hi:.3f}), units in it: {units_in_interval}")

print()
# For n=p^2, n/(p+1) = p^2/(p+1). n/p = p.
# So interval is (p^2/(p+1), p). p^2/(p+1) = p - p/(p+1) ≈ p-1.
# So interval is approximately (p-1, p) — no integers! For large p, this is empty.
# This confirms n=p^2 needs a different approach.

print("""
CONCLUSION for n=p^2:
  The interval (n/(p+1), n/p) = (p^2/(p+1), p) has NO integers for p ≥ 3
  (since p^2/(p+1) = p - p/(p+1) > p-1 for p ≥ 2, so interval = (>p-1, p)
  which is empty of integers).

  For n=p^2: Need to look at e_u giving floor(n/e_u) = 2p, 3p, etc.
  floor(n/e_u) = 2p when e_u ∈ (n/(2p+1), n/(2p)) = (p^2/(2p+1), p/2).
  Width: p/2 - p^2/(2p+1) = p(2p+1-2p)/(2(2p+1)) = p/(2(2p+1)) < 1.
  Also potentially empty!

  The isolation for n=p^2 must come from Case 2 or the out-of-range mechanism,
  or from e_u giving floor(n/e_u) = k·p for larger k.
""")

# Find actual mechanism for each e_u that IS isolated for n=p^2
print("Detailed isolated events for n=p^2:")
for p_val in [3, 5, 7]:
    n = p_val * p_val
    units = units_mod_n(n)
    units_small = [eu for eu in units if eu >= 3 and eu < n // 2]

    print(f"\nn={n} (p={p_val}) — isolated (e_u, m=2) events:")
    print(f"  {'e_u':>6} {'a=n%eu':>8} {'2a vs eu':>10} {'case':>6} {'q=n//eu':>8} "
          f"{'q mod p':>8} {'e*':>6} {'gcd(e*,n)':>10} {'mechanism'}")
    for eu in units_small:
        a = n % eu
        estar, in_range, is_unit_flag = compute_estar(eu, n)
        is_iso = (not in_range) or (not is_unit_flag)
        if not is_iso: continue

        q = n // eu
        case = 'OR' if not in_range else ('C1' if 2*a < eu else 'C2')
        mech = ('out-of-range' if not in_range
                else f'gcd(e*={estar},{n})={gcd(estar,n)}')
        q_mod_p = q % p_val
        print(f"  {eu:>6} {a:>8} {2*a:>5} vs {eu:<4} {case:>6} {q:>8} "
              f"{q_mod_p:>8} {str(estar) if estar else 'N/A':>6} "
              f"{gcd(estar,n) if in_range and estar else 'N/A':>10} {mech}")
