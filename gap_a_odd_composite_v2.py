"""
gap_a_odd_composite_v2.py
=========================
CORRECTED four-part investigation of Gap A for odd composite n.

CORRECTED e'* formula (v1 had wrong range [n-eu, n-2]; correct is [n-eu, n-1]):

  For m=2 and any unit e_u ≥ 3:
    Cond1 never fires (needs eu | 1, impossible for eu ≥ 2).
    Cond2 fires iff ∃ unit e' in [n-eu, n-1] with e' ≡ -n (mod eu).

  Unique solution e'* in [n-eu, n-1]:
    a = n mod eu  (1 ≤ a ≤ eu-1)
    If 2a ≤ eu:  e'* = n - 2a    (includes boundary 2a=eu: e'*=n-eu)
    If 2a > eu:  e'* = n + eu - 2a

  SPECIAL CASE 2a = eu+1: e'* = n-1.  gcd(n-1, n) = 1 ALWAYS.
    → Cond2 always fires → NOT isolated.
    (v1 wrongly said "out of range". n-1 ≤ n-1 is in [n-eu, n-1].)

  (e_u, 2) isolated iff gcd(e'*, n) > 1.

  Key: e'* = n - 2a (Case 1) → isolated iff p | (n-2a) iff p | 2a iff p | a
              (since p|n) iff p | (n mod eu) iff p | eu·floor(n/eu) iff p|floor(n/eu).
       e'* = n + eu - 2a (Case 2, 2a > eu+1) → isolated iff p | (eu - 2a + eu) = p|(eu-2a).
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

def covers_via_cond(ep, eu, m, n):
    s = (ep * m) % eu
    if ep < eu and s == ep: return True, 1
    if ep + eu >= n and s == (ep + eu - n): return True, 2
    return False, 0

def is_isolated_m2_brute(eu, n, units):
    """Brute-force: (e_u, m=2) isolated iff no unit e' fires Cond2."""
    for ep in units:
        if ep == eu: continue
        fired, cnum = covers_via_cond(ep, eu, 2, n)
        if fired and cnum == 2: return False
    return True

def compute_estar_v2(eu, n):
    """
    CORRECTED formula. Range is [n-eu, n-1].
    Returns (e_star, is_unit_flag).
    is_unit_flag = gcd(e_star, n) == 1.
    """
    a = n % eu  # 1 <= a <= eu-1
    two_a = 2 * a
    if two_a <= eu:    # Case 1 + boundary (2a=eu)
        estar = n - two_a
    else:              # Case 2 (2a > eu), including 2a = eu+1 → estar = n-1
        estar = n + eu - two_a
    is_unit = gcd(estar, n) == 1
    return estar, is_unit

def is_isolated_m2_formula(eu, n):
    """Formula prediction: isolated iff gcd(e'*, n) > 1."""
    _, is_unit = compute_estar_v2(eu, n)
    return not is_unit

# ============================================================
print("=" * 70)
print("PART A: CORRECTED Formula Verification")
print("  Claim: (e_u, 2) isolated ↔ gcd(e'*, n) > 1")
print("  Range corrected to [n-eu, n-1]; no 'out-of-range' case.")
print("=" * 70)

total_checks = 0
mismatches = 0

for n in range(9, 101, 2):
    if phi(n) == n - 1: continue  # skip primes
    units = units_mod_n(n)
    for eu in units:
        if eu < 3: continue

        actual = is_isolated_m2_brute(eu, n, units)
        formula = is_isolated_m2_formula(eu, n)
        total_checks += 1
        if formula != actual:
            mismatches += 1
            estar, is_unit = compute_estar_v2(eu, n)
            print(f"  MISMATCH: n={n} e_u={eu} a={n%eu} e*={estar} "
                  f"gcd={gcd(estar,n)} formula={formula} actual={actual}")

print(f"\nChecked {total_checks} (e_u, m=2) events for odd composite n in [9,100].")
print(f"Mismatches: {mismatches}")
if mismatches == 0:
    print("  ✓ CORRECTED FORMULA VERIFIED — zero mismatches.")

# Case breakdown
out_of_range_v1_count = 0  # 2a = eu+1 (the formerly-misclassified cases)
case1_iso = 0  # 2a < eu, gcd(e'*,n)>1
case2_iso = 0  # 2a > eu (not eu+1), gcd(e'*,n)>1
case1_not_iso = 0
case2_not_iso = 0
eu1_count = 0  # 2a = eu+1 (always NOT isolated)

for n in range(9, 61, 2):
    if phi(n) == n - 1: continue
    units = units_mod_n(n)
    for eu in units:
        if eu < 3: continue
        a = n % eu
        two_a = 2 * a
        estar, is_unit = compute_estar_v2(eu, n)
        is_iso = not is_unit
        if two_a == eu + 1:
            eu1_count += 1
        elif two_a <= eu:
            if is_iso: case1_iso += 1
            else: case1_not_iso += 1
        else:
            if is_iso: case2_iso += 1
            else: case2_not_iso += 1

print(f"\nCase breakdown (all units eu≥3, odd composite n≤60):")
print(f"  2a = eu+1 (e*=n-1, always unit, NEVER isolated):  {eu1_count}")
print(f"  2a ≤ eu (Case 1): isolated={case1_iso}, not isolated={case1_not_iso}")
print(f"  2a > eu+1 (Case 2): isolated={case2_iso}, not isolated={case2_not_iso}")

# Per-n summary (ALL units eu≥3, not just eu < n/2)
print("\nPer-n summary (ALL units e_u≥3, odd composite n ≤ 60):")
print(f"{'n':>5} {'p':>4} {'all_units≥3':>12} {'case1_iso':>10} {'case2_iso':>10} "
      f"{'total_iso_m2':>13} {'any?':>8}")
print("-" * 70)

for n in range(9, 61, 2):
    if phi(n) == n - 1: continue
    units = units_mod_n(n)
    p = smallest_prime(n)

    all_units_ge3 = [eu for eu in units if eu >= 3]
    c1_iso = c2_iso = 0
    for eu in all_units_ge3:
        a = n % eu
        two_a = 2 * a
        estar, is_unit = compute_estar_v2(eu, n)
        is_iso = not is_unit
        if is_iso:
            if two_a <= eu: c1_iso += 1
            elif two_a != eu + 1: c2_iso += 1
    total_iso = c1_iso + c2_iso
    print(f"n={n:>4} p={p:<4} {len(all_units_ge3):>12} {c1_iso:>10} {c2_iso:>10} "
          f"{total_iso:>13} {'YES' if total_iso > 0 else '*** NO ***':>8}")


# ============================================================
print("\n" + "=" * 70)
print("PART B: e'* Structure for Case 1 vs Case 2")
print("  Case 1 (2a < eu): e'* = n-2a. Isolated iff p | a iff p | floor(n/eu).")
print("  Case 2 (2a > eu+1): e'* = n+eu-2a. Isolated iff p | (eu-2a).")
print("  Case 2a=eu+1: e'*=n-1, always unit → never isolated.")
print("=" * 70)

print("\nFor n=p^2 (p=3,5,7): floor(n/eu) mod p distribution for ALL units eu≥3:")
for p_val in [3, 5, 7]:
    n = p_val * p_val
    units = units_mod_n(n)
    all_units_ge3 = [eu for eu in units if eu >= 3]

    print(f"\nn={n} (p={p_val}), {len(all_units_ge3)} units eu≥3:")
    print(f"  {'eu':>5} {'a':>4} {'2a':>4} {'eu':>4} {'case':>4} {'q=n//eu':>8} "
          f"{'q mod p':>8} {'e*':>6} {'gcd(e*,n)':>10} {'iso?':>6}")
    for eu in all_units_ge3:
        a = n % eu
        two_a = 2 * a
        estar, is_unit = compute_estar_v2(eu, n)
        is_iso = not is_unit
        q = n // eu
        q_mod_p = q % p_val
        if two_a <= eu: case = 'C1'
        elif two_a == eu + 1: case = 'C1*'
        else: case = 'C2'
        mark = '<-- ISO' if is_iso else ''
        print(f"  {eu:>5} {a:>4} {two_a:>4} {eu:>4} {case:>4} {q:>8} "
              f"{q_mod_p:>8} {estar:>6} {gcd(estar,n):>10} {str(is_iso):>6} {mark}")


# ============================================================
print("\n" + "=" * 70)
print("PART C: Revised — Does every odd composite n have ≥1 isolated (eu,2) event?")
print("  Check ALL units eu≥3 (not just eu < n/2).")
print("=" * 70)

failures = []
iso_counts = []

for n in range(9, 201, 2):
    if phi(n) == n - 1: continue
    p = smallest_prime(n)
    units = units_mod_n(n)
    all_units_ge3 = [eu for eu in units if eu >= 3]

    iso_m2 = sum(1 for eu in all_units_ge3 if is_isolated_m2_formula(eu, n))

    if iso_m2 == 0:
        failures.append(n)
    iso_counts.append((n, p, len(all_units_ge3), iso_m2))

print(f"\nChecked all odd composite n in [9, 200]:")
print(f"  Odd composite n with ZERO isolated m=2 events: {failures}")
if not failures:
    print("  ✓ EVERY odd composite n ≤ 200 has at least one isolated (eu,2) event!")

print("\nPer-n table (selected):")
print(f"{'n':>5} {'p':>4} {'units≥3':>8} {'iso_m2':>8} {'mechanism'}")
print("-" * 55)
for n, p, ucnt, iso in iso_counts:
    if n <= 60 or n in [81, 121, 125, 169, 175, 189]:
        units = units_mod_n(n)
        all_units_ge3 = [eu for eu in units if eu >= 3]
        # what mechanism?
        mechs = []
        for eu in all_units_ge3:
            a = n % eu
            two_a = 2 * a
            estar, is_unit = compute_estar_v2(eu, n)
            if not is_unit:
                if two_a <= eu: mechs.append(f'C1(eu={eu})')
                else: mechs.append(f'C2(eu={eu})')
        mech_str = ', '.join(mechs[:3]) + (f'... (+{len(mechs)-3})' if len(mechs) > 3 else '')
        print(f"n={n:>4} p={p:<4} {ucnt:>8} {iso:>8}   {mech_str}")


# ============================================================
print("\n" + "=" * 70)
print("PART D: Tight Cases — minimum isolation count among all units eu≥3")
print("=" * 70)

tight_cases = []
for n in range(9, 201, 2):
    if phi(n) == n - 1: continue
    p = smallest_prime(n)
    units = units_mod_n(n)
    all_units_ge3 = [eu for eu in units if eu >= 3]
    if not all_units_ge3:
        continue

    iso_m2 = c1 = c2 = 0
    for eu in all_units_ge3:
        a = n % eu
        two_a = 2 * a
        estar, is_unit = compute_estar_v2(eu, n)
        is_iso = not is_unit
        if is_iso:
            iso_m2 += 1
            if two_a <= eu: c1 += 1
            else: c2 += 1
    ratio = iso_m2 / len(all_units_ge3)
    tight_cases.append((iso_m2, n, p, len(all_units_ge3), c1, c2, ratio))

tight_cases.sort()

print(f"\n{'iso_m2':>8} {'n':>6} {'p':>4} {'units≥3':>8} {'C1_iso':>7} "
      f"{'C2_iso':>7} {'ratio':>8}")
print("-" * 55)
for iso_m2, n, p, ucnt, c1, c2, ratio in tight_cases[:30]:
    print(f"{iso_m2:>8} {n:>6} {p:>4} {ucnt:>8} {c1:>7} {c2:>7} {ratio:>8.4f}")

print(f"\nMinimum isolated m=2 count: {tight_cases[0][0]}")
print(f"  At n={tight_cases[0][1]}, p={tight_cases[0][2]}")
zero_iso = [n for iso, n, *_ in tight_cases if iso == 0]
print(f"Odd composite n with zero isolated m=2 events: {zero_iso if zero_iso else 'NONE'}")


# ============================================================
print("\n" + "=" * 70)
print("PART D.2: n=p^2 anatomy (tightest cases)")
print("=" * 70)

for p_val in [3, 5, 7, 11, 13]:
    n = p_val * p_val
    units = units_mod_n(n)
    all_units_ge3 = [eu for eu in units if eu >= 3]
    total = len(all_units_ge3)
    if total == 0:
        print(f"\nn={n} (p={p_val}): no units eu≥3 (boundary case)")
        continue

    iso = sum(1 for eu in all_units_ge3 if is_isolated_m2_formula(eu, n))
    pct = 100 * iso // total

    # Mechanism breakdown
    c1_iso = sum(1 for eu in all_units_ge3
                 if is_isolated_m2_formula(eu, n) and 2*(n%eu) <= eu)
    c2_iso = iso - c1_iso

    print(f"\nn={n} (p={p_val}): {iso}/{total} = {pct}% isolated m=2 events")
    print(f"  Case 1 isolated: {c1_iso}, Case 2 isolated: {c2_iso}")

    # Show the specific isolated events
    print(f"  Isolated events:")
    for eu in all_units_ge3:
        estar, is_unit = compute_estar_v2(eu, n)
        if not is_unit:
            a = n % eu
            two_a = 2 * a
            q = n // eu
            case = 'C1' if two_a <= eu else 'C2'
            print(f"    eu={eu:>3}, a={a:>3}, q=n//eu={q:>3}, q mod p={q%p_val}, "
                  f"e*={estar:>4}, gcd(e*,n)={gcd(estar,n)}, case={case}")


# ============================================================
print("\n" + "=" * 70)
print("PART E: Corrected Theorem Assembly")
print("=" * 70)

print("""
CORRECTED THEOREMS (from PART A verification):

Theorem A (Corrected Formula). For odd composite n and unit eu ≥ 3:
  Let a = n mod eu (1 ≤ a ≤ eu-1). The unique Cond2 partner is:
    e'* = n - 2a       if 2a ≤ eu  (Case 1)
    e'* = n + eu - 2a  if 2a > eu  (Case 2, including 2a=eu+1 → e'*=n-1)
  e'* is always in [n-eu, n-1].
  (eu, m=2) is isolated iff gcd(e'*, n) > 1 (i.e., e'* is non-unit).

  SPECIAL: When 2a = eu+1, e'* = n-1. Since gcd(n-1, n)=1 always, the event is
  NEVER isolated. (v1 script wrongly claimed "out of range". Corrected here.)

Theorem B (Case 1 isolation criterion). If 2a < eu:
  e'* = n - 2a. Isolated iff p | (n-2a). Since p|n: p|2a, i.e., p|a (p odd).
  Since a = n mod eu = n - eu·q where q = floor(n/eu):
    p|a ↔ p|(n - eu·q) ↔ p|eu·q ↔ p|q  (since gcd(eu,n)=1 → gcd(eu,p)=1).
  So: (eu, m=2) isolated in Case 1 iff p | floor(n/eu).

Theorem C (Case 2 isolation criterion). If 2a > eu+1:
  e'* = n + eu - 2a. Isolated iff p | (eu - 2a).
  (Since p|n: p|(n+eu-2a) ↔ p|(eu-2a).)

Theorem D (Never-isolated case). If 2a = eu+1:
  e'* = n-1, always a unit. NEVER isolated.

GAP A STATUS FOR ODD COMPOSITE n (revised):

Part C confirms: EVERY odd composite n ≤ 200 has ≥1 isolated (eu, m=2) event
when searching all units eu≥3 (not just eu < n/2).

The proof strategy: For any odd composite n with smallest prime p,
find a unit eu such that gcd(e'*, n) > 1.

CASE 1 PATH: Find unit eu with p | floor(n/eu).
  - For n = p·q (q≥p+2): interval (n/(p+1), n/p) has width q/(p+1) > 1.
    Any integer in this interval gives floor(n/eu) = p ≡ 0 (mod p).
    Need this integer to be a unit — likely (need gcd check).
  - For n = p^2: interval (p^2/(p+1), p) = (p-p/(p+1), p) has NO integers.
    Need higher multiples: floor(n/eu) = 2p, 3p, etc.
    Data shows these DO exist for all tested n=p^2 (via Case 2 instead).

CASE 2 PATH: Find unit eu with p | (eu - 2a).
  eu ≡ 2a (mod p). Since a = n mod eu and p|n: a ≡ n mod eu (mod p).
  Need to find eu with eu ≡ 2(n mod eu) mod p.
  Data shows Case 2 provides isolation for n=p^2 (n=25, 49, 121, 169 all have
  isolated events from Case 2).
""")

# Verify: for each n=p^2 up to 400, find the mechanism
print("Verification — n=p^2, mechanism of first isolated m=2 event:")
print(f"{'n':>6} {'p':>4} {'eu':>5} {'a':>4} {'q=n//eu':>8} {'case':>5} {'e*':>6} {'gcd':>5}")
for p_val in range(3, 25, 2):
    if not all(p_val % d != 0 for d in range(2, p_val)): continue  # skip non-primes
    n = p_val * p_val
    units = units_mod_n(n)
    found = False
    for eu in sorted(e for e in units if e >= 3):
        estar, is_unit = compute_estar_v2(eu, n)
        if not is_unit:
            a = n % eu
            two_a = 2 * a
            q = n // eu
            case = 'C1' if two_a <= eu else 'C2'
            print(f"n={n:>5} p={p_val:>3} eu={eu:>4} a={a:>4} q={q:>7} {case:>5} e*={estar:>5} gcd={gcd(estar,n):>4}")
            found = True
            break
    if not found:
        print(f"n={n:>5} p={p_val:>3}: NO isolated m=2 event found!")

print("""
KEY OBSERVATION from n=p^2 data:
  For n=p^2, the first isolated (eu, m=2) event often has eu just above p.
  Specifically: eu = p+2 (the next unit after p, which is non-unit).
  For eu = p+2: a = n mod (p+2) = p^2 mod (p+2).
    p^2 = (p+2)(p-2) + 4, so a = 4 (for p > 4).
    q = floor(p^2/(p+2)) = p-2.
    2a = 8. Case: 2a < eu iff 8 < p+2 iff p > 6. So Case 1 for p ≥ 7.
    e'* = n - 2a = p^2 - 8.
    gcd(p^2 - 8, p^2) = gcd(-8, p^2) = gcd(8, p^2).
    For odd prime p: gcd(8, p^2) = 1. NOT isolated!
  So eu = p+2 fails. Need to look further.
""")
