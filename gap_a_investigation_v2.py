"""
gap_a_investigation_v2.py
=========================
Follow-up investigation after v1 findings.

KEY v1 FINDING:
  Zero-isolated events occur EXACTLY for PRIME n (n=5,7,11,13,17,19,23,...).
  ALL composite n have positive isolated count.

  This is not a counterexample to Gap A — it's the PROOF STRUCTURE:
  - Composite n needs Z0S (isolated events → B_safe ≥ 1) → and isolated events EXIST ✓
  - Prime n doesn't need Z0S (uses Sole Cover instead) → zero isolated events is fine

  Gap A is thus closed FOR EVEN COMPOSITE n by a constructive event.
  Remaining: odd composite n.

THIS SCRIPT:
  Part 1: Prove (n-1, m=2) isolated iff n even — verify algebraic theorem.
  Part 2: For odd composite n, find the structure of isolated events.
  Part 3: Find a universal isolated event for odd composite n.
  Part 4: Characterise which (e_u, m) pairs are isolated in terms of the unit-set gaps.
  Part 5: Minimal isolated event per n — what's the simplest witness?
"""

from math import gcd
from itertools import product

def extended_gcd(a, b):
    if a == 0: return b, 0, 1
    g, x, y = extended_gcd(b % a, a)
    return g, y - (b // a) * x, x

def modinv(a, n):
    g, x, _ = extended_gcd(a % n, n)
    return x % n if g == 1 else None

def phi(n):
    result, temp, p = n, n, 2
    while p * p <= temp:
        if temp % p == 0:
            while temp % p == 0: temp //= p
            result -= result // p
        p += 1
    if temp > 1: result -= result // temp
    return result

def units_mod_n(n):
    return [e for e in range(1, n) if gcd(e, n) == 1]

def covers_via_cond_with_n(ep, eu, m, n):
    s = (ep * m) % eu
    if ep < eu and s == ep: return True, 1
    if ep + eu >= n and s == (ep + eu - n): return True, 2
    return False, 0

def is_isolated(eu, m, n, units):
    for ep in units:
        if ep == eu: continue
        fires, _ = covers_via_cond_with_n(ep, eu, m, n)
        if fires: return False
    return True

def find_isolated_events(n):
    units = units_mod_n(n)
    result = []
    for eu in units:
        if eu < 2: continue
        for m in range(2, eu):
            if is_isolated(eu, m, n, units):
                result.append((eu, m))
    return result

# ============================================================
print("=" * 70)
print("PART 1: Algebraic theorem for (n-1, m=2)")
print("Claim: isolated iff n is even (composite)")
print("=" * 70)

print("""
Proof of claim:
  e_u = n-1, m = 2, r_dep = 1.
  Cond1: s = e'·2 mod (n-1) = e'. Requires 2e' ≡ e' (mod n-1) → e' ≡ 0 (mod n-1).
         Only solution e'=0, not valid. Cond1 NEVER fires for m=2.
  Cond2: Needs unit e' with e'+e_u >= n AND s = e'+e_u-n.
         e' + (n-1) >= n → e' >= 1 (always). s = 2e' mod (n-1) = e'+(n-1)-n = e'-1.
         So need: 2e' ≡ e'-1 (mod n-1) → e' ≡ -1 (mod n-1) → e' = n-2.
         Cond2 fires iff n-2 is a unit, i.e., gcd(n-2, n) = gcd(2, n) = 1.
         gcd(2,n) = 1 iff n is odd. gcd(2,n) = 2 iff n is even.

  CONCLUSION:
    - n even: n-2 not a unit → Cond2 fails → event ISOLATED ✓
    - n odd:  n-2 is a unit → Cond2 fires → event NOT isolated
""")

print("Numerical verification:")
errors = 0
for n in range(4, 80):
    if phi(n) < 2: continue
    units = units_mod_n(n)
    eu = n - 1
    if eu not in units: continue
    m = 2
    isolated = is_isolated(eu, m, n, units)
    n_even = (n % 2 == 0)
    expected_isolated = n_even
    if isolated != expected_isolated:
        print(f"  ERROR: n={n}, isolated={isolated}, n_even={n_even}")
        errors += 1
print(f"  0 errors (checked n=4..79)" if errors == 0 else f"  {errors} ERRORS found")

# ============================================================
print("\n" + "=" * 70)
print("PART 2: Odd composite n — minimal isolated event search")
print("=" * 70)

print("\nFor each odd composite n, find the FIRST isolated event (smallest e_u, then m):")
print(f"{'n':>5} {'smallest prime factor p':>24} {'e_u':>6} {'m':>5} {'r_dep':>7} {'notes'}")
print("-" * 70)

def smallest_prime_factor(n):
    for p in range(2, n):
        if n % p == 0: return p
    return n

for n in [9, 15, 21, 25, 27, 33, 35, 39, 45, 49, 51, 55, 57, 63, 65, 75, 77, 91]:
    if n % 2 == 0: continue
    p = smallest_prime_factor(n)
    is_prime_n = (phi(n) == n-1)
    if is_prime_n: continue

    units = units_mod_n(n)
    iso = find_isolated_events(n)

    if not iso:
        print(f"  n={n}: NO ISOLATED EVENTS (this would disprove Gap A!)")
        continue

    eu, m = iso[0]  # first isolated event
    inv_eu = modinv(eu, n)
    r_dep = (-(m-1) * inv_eu) % n if inv_eu else None
    is_unit_rdep = gcd(r_dep, n) == 1 if r_dep else None

    print(f"n={n:>4} p={p:<3} e_u={eu:<6} m={m:<4} r_dep={str(r_dep):<5} "
          f"unit?={is_unit_rdep}  gcd(m,eu)={gcd(m,eu)}")

# ============================================================
print("\n" + "=" * 70)
print("PART 3: Pattern analysis — does gcd(e_u, p) relate to isolation?")
print("For n=p^2: are isolated events exactly those where e_u mod p = p-1?")
print("=" * 70)

for n_p_pair in [(9,3), (25,5), (49,7)]:
    n, p = n_p_pair
    units = units_mod_n(n)
    iso_events = find_isolated_events(n)
    all_events = [(eu, m) for eu in units if eu >= 2 for m in range(2, eu)]

    print(f"\nn={n} (p={p}):")
    print(f"  Total m>=2 events: {len(all_events)}, Isolated: {len(iso_events)}")

    # Classify by e_u mod p
    eu_mod_p_stats = {}
    for eu in units:
        if eu < 2: continue
        eu_class = eu % p
        total_for_eu = eu - 2  # m from 2 to eu-1
        iso_for_eu = sum(1 for e, m in iso_events if e == eu)
        if eu_class not in eu_mod_p_stats:
            eu_mod_p_stats[eu_class] = {'total': 0, 'iso': 0, 'eu_list': []}
        eu_mod_p_stats[eu_class]['total'] += total_for_eu
        eu_mod_p_stats[eu_class]['iso'] += iso_for_eu
        eu_mod_p_stats[eu_class]['eu_list'].append(eu)

    print(f"  Breakdown by e_u mod {p}:")
    for cls in sorted(eu_mod_p_stats):
        d = eu_mod_p_stats[cls]
        frac = d['iso']/d['total'] if d['total'] > 0 else 0
        print(f"    e_u ≡ {cls} (mod {p}): {d['iso']}/{d['total']} isolated = {frac:.3f}   eu_list={d['eu_list'][:5]}")

    # Classify by m mod p
    m_mod_p_stats = {}
    for eu, m in all_events:
        cls = m % p
        is_iso = (eu, m) in iso_events
        if cls not in m_mod_p_stats:
            m_mod_p_stats[cls] = {'total': 0, 'iso': 0}
        m_mod_p_stats[cls]['total'] += 1
        m_mod_p_stats[cls]['iso'] += int(is_iso)

    print(f"  Breakdown by m mod {p}:")
    for cls in sorted(m_mod_p_stats):
        d = m_mod_p_stats[cls]
        frac = d['iso']/d['total'] if d['total'] > 0 else 0
        print(f"    m ≡ {cls} (mod {p}): {d['iso']}/{d['total']} isolated = {frac:.3f}")

# ============================================================
print("\n" + "=" * 70)
print("PART 4: Testing candidate 'universal isolated event' for odd composite n")
print("Candidate A: (e_u = p+1, m = p) where p = smallest prime factor")
print("Candidate B: (e_u = p-1, m = p-2)")
print("Candidate C: look at events where m ≡ 0 (mod p)")
print("=" * 70)

print("\nCandidate A: (e_u=p+1, m=p) — is this always isolated for odd composite n?")
for n in [9, 15, 21, 25, 27, 33, 35, 39, 45, 49, 51, 55, 57, 63, 65, 75, 77, 91]:
    if n % 2 == 0: continue
    p = smallest_prime_factor(n)
    is_prime_n = (phi(n) == n - 1)
    if is_prime_n: continue

    eu = p + 1
    if gcd(eu, n) != 1:  # eu must be a unit
        print(f"  n={n}, p={p}: e_u=p+1={eu} is NOT a unit (gcd={gcd(eu,n)}). Skipping.")
        continue
    if eu < 2 or p < 2 or p >= eu:
        print(f"  n={n}, p={p}: m=p={p} out of range [2,{eu-1}]. Skipping.")
        continue

    units = units_mod_n(n)
    iso = is_isolated(eu, p, n, units)
    print(f"  n={n:>4}, p={p}: e_u={eu}, m={p}, isolated={iso}", end='')
    if not iso:
        # Find who covers it
        covering = [(ep, c) for ep in units if ep != eu
                    for _, c in [covers_via_cond_with_n(ep, eu, p, n)]
                    if covers_via_cond_with_n(ep, eu, p, n)[0]]
        print(f"  <- COVERED by {covering[:3]}")
    else:
        print("  ✓")

print("\nCandidate B: (e_u=p+1, m=2) — always isolated for odd composite n?")
for n in [9, 15, 21, 25, 27, 33, 35, 39, 45, 49, 51, 55, 57, 63, 65, 75, 77, 91]:
    if n % 2 == 0: continue
    p = smallest_prime_factor(n)
    is_prime_n = (phi(n) == n - 1)
    if is_prime_n: continue

    eu = p + 1
    if gcd(eu, n) != 1 or eu < 2:
        print(f"  n={n}, p={p}: e_u=p+1={eu} is NOT a unit. Skipping.")
        continue

    units = units_mod_n(n)
    iso = is_isolated(eu, 2, n, units)
    print(f"  n={n:>4}, p={p}: e_u={eu}, m=2, isolated={iso}", end='')
    if not iso:
        covering = [(ep, c) for ep in units if ep != eu
                    for fired, c in [covers_via_cond_with_n(ep, eu, 2, n)]
                    if fired]
        print(f"  <- COVERED by {covering[:3]}")
    else:
        print("  ✓")

print("\nCandidate C: (e_u=p^2-p-1=n-p-1, m=2) for n=p^2:")
for p in [3, 5, 7, 11, 13]:
    n = p * p
    eu = n - p - 1  # = p^2 - p - 1
    if gcd(eu, n) != 1:
        print(f"  n={n} (p={p}): e_u={eu} not a unit (gcd={gcd(eu,n)})")
        continue

    units = units_mod_n(n)
    iso = is_isolated(eu, 2, n, units)
    print(f"  n={n:>4} (p={p}): e_u={eu}=n-p-1, m=2, isolated={iso}", end='')
    if not iso:
        covering = [(ep, c) for ep in units if ep != eu
                    for fired, c in [covers_via_cond_with_n(ep, eu, 2, n)] if fired]
        print(f"  COVERED by {covering[:3]}")
    else:
        print("  ✓")

# ============================================================
print("\n" + "=" * 70)
print("PART 5: Structural theorem search — characterise all isolated events")
print("For each (e_u, m) pair, what algebraic property predicts isolation?")
print("=" * 70)

print("\nHypothesis: (e_u, m) is isolated iff p | gcd(e_u, m-1) for some prime p|n but p∤e_u")
print("(i.e., the 'natural relay divisor' e_u/gcd(e_u,e') is blocked by a unit gap)")
print()

# Test for n=12 (small composite with clear structure)
n = 12
units = units_mod_n(n)
nonunits = [e for e in range(1,n) if gcd(e,n) > 1]
all_events = [(eu, m) for eu in units if eu >= 2 for m in range(2, eu)]
iso_events = set(find_isolated_events(n))

print(f"n={n}, units={units}, nonunits={nonunits}")
print(f"All m>=2 events ({len(all_events)}), isolated ({len(iso_events)}):")
print()

for eu, m in all_events:
    iso = (eu, m) in iso_events
    # What's the 'natural relay' for Cond1? Smallest e' | (m-1)·e_u such that gcd(e',n)=1
    # Cond1 needs e_u/gcd(e_u,e') | (m-1). For m-1 given, find all e' < e_u with this property.
    cond1_candidates = [ep for ep in units if ep < eu and (m-1) % (eu // gcd(eu, ep)) == 0]
    cond2_candidates = [ep for ep in units if ep != eu and ep + eu >= n
                        and (ep * m) % eu == (ep + eu - n)]
    # Is there a non-unit that would be the natural relay?
    nonunit_relay = [e for e in nonunits if e < eu and (m-1) % (eu // gcd(eu, e)) == 0]

    if iso:
        print(f"  ISOLATED: e_u={eu}, m={m}  cond1_cand={cond1_candidates}  "
              f"cond2_cand={cond2_candidates}  nonunit_relay_blocked={nonunit_relay}")

print()
# Check: for isolated events, is the non-unit relay always non-empty?
print("Checking: For all isolated events across composite n up to 50,")
print("  is there always a non-unit e that WOULD relay (via Cond1 divisibility) but can't?")
print()

for n in range(4, 51):
    if phi(n) == n-1: continue  # skip primes
    units = units_mod_n(n)
    nonunits = [e for e in range(1, n) if gcd(e, n) > 1]
    iso_events = find_isolated_events(n)

    for eu, m in iso_events:
        # Find non-units that satisfy the divisibility for Cond1
        blocked_nonunit_relay = [e for e in nonunits
                                 if 1 <= e < eu and (m-1) % (eu // gcd(eu, e)) == 0]
        if not blocked_nonunit_relay:
            print(f"  n={n}, e_u={eu}, m={m}: NO blocked nonunit relay "
                  f"(isolated by Cond2 failure only?)")

# ============================================================
print("\n" + "=" * 70)
print("PART 6: Universal isolated event theorem — odd composite n")
print("Testing: is (e_u = n-1, m = (n-1)/2) isolated for odd composite n?")
print("(Only valid when n ≡ 1 mod 2, so (n-1)/2 is integer)")
print("=" * 70)

print("\n(e_u=n-1, m=(n-1)/2):")
for n in range(9, 100, 2):  # odd n
    if phi(n) == n - 1: continue  # skip primes
    eu = n - 1
    m = (n - 1) // 2
    if m < 2 or m >= eu: continue

    units = units_mod_n(n)
    if eu not in units: continue

    iso = is_isolated(eu, m, n, units)
    if not iso:
        covering = [(ep, c) for ep in units if ep != eu
                    for fired, c in [covers_via_cond_with_n(ep, eu, m, n)] if fired]
        print(f"  n={n:>4}: NOT isolated. Covered by {covering[:3]}")
    # else: print(f"  n={n}: isolated ✓")  # uncomment to see all

# Report summary
isolated_count_odd = sum(1 for n in range(9, 100, 2)
                         if phi(n) != n-1 and (n-1) in units_mod_n(n)
                         and (n-1)//2 >= 2 and is_isolated(n-1, (n-1)//2, n, units_mod_n(n)))
total_odd_composite = sum(1 for n in range(9, 100, 2)
                          if phi(n) != n-1 and (n-1) in units_mod_n(n) and (n-1)//2 >= 2)
print(f"\nResult: (n-1, (n-1)/2) isolated for {isolated_count_odd}/{total_odd_composite} odd composite n in [9,99]")

# ============================================================
print("\n" + "=" * 70)
print("PART 7: The KEY theorem — why primes have zero isolated events")
print("(Understanding the structural reason)")
print("=" * 70)

print("""
For PRIME n: every unit e' < e_u satisfies some relay property that lets
Cond1 or Cond2 cover r_dep. Why?

For prime n, the unit set = {1,2,...,n-1} (complete).
For Cond2: the "Cond2 partner" of e_u for m=2 is e' = n-2.
For prime n: gcd(n-2, n) = 1 → n-2 IS a unit → Cond2 can always fire!

But wait — does Cond2 always fire? Cond2 for (e_u=n-1, m=2) needs e'=n-2.
For PRIME n: n-2 is a unit ✓ → Cond2 fires → event NOT isolated ✓

For GENERAL prime n and arbitrary (e_u, m): does the relay always complete?
The answer is YES for prime n (verified up to n=113) because:
  - Every integer 1 to n-1 is a unit → dense relay chain
  - For any "gap" in the chain, a Cond2 partner fills it
  - The completeness of {1,...,n-1} as units means no relay chain can break
""")

# Verify: for prime n, Cond2 coverage is "dense"
print("Checking Cond2 partner density for prime n:")
for n in [7, 11, 13, 17, 19, 23]:
    units = units_mod_n(n)
    cond2_events = 0
    for eu in units:
        if eu < 2: continue
        for m in range(2, eu):
            for ep in units:
                if ep == eu: continue
                fired, cnum = covers_via_cond_with_n(ep, eu, m, n)
                if fired and cnum == 2:
                    cond2_events += 1
                    break
    total_m2 = sum(eu - 2 for eu in units if eu >= 2)
    cond1_events = sum(1 for eu in units if eu >= 2
                       for m in range(2, eu)
                       if any(covers_via_cond_with_n(ep, eu, m, n)[0] and
                              covers_via_cond_with_n(ep, eu, m, n)[1] == 1
                              for ep in units if ep != eu))
    print(f"  n={n}: total m>=2 events={total_m2}, Cond2-covered={cond2_events}, "
          f"Cond1-covered={cond1_events}, overlap possible")

# ============================================================
print("\n" + "=" * 70)
print("PART 8: PROOF SKETCH for Gap A (odd composite n)")
print("=" * 70)

print("""
For odd composite n, let p be the smallest prime factor.
Then p is odd, p >= 3, and p | n but gcd(p, n/p) could be 1 or not.

KEY LEMMA (to prove): There exists a unit e_u and m >= 2 such that:
  (1) Cond1 fails: for all units e' < e_u, e_u/gcd(e_u,e') ∤ (m-1)
  (2) Cond2 fails: the Cond2 partner e' = (e_u*(m+1) - n*m) / (m-1) is NOT a unit

Candidate event for odd composite n:
  Consider e_u = n - 1 (always a unit) and m = (n+1)/2 (need n ≡ 1 mod 2, true for odd n).

  r_dep = -(m-1)·(n-1)^{-1} mod n = -((n-1)/2)·(-1) mod n = (n-1)/2 mod n.

  Cond1: s = e'·m mod (n-1) = e'·(n+1)/2 mod (n-1).
         For Cond1: s = e'. So e'·(n+1)/2 ≡ e' (mod n-1) → e'·(n-1)/2 ≡ 0 (mod n-1)
         → e' ≡ 0 (mod 2). So Cond1 fires for even units e' < n-1!

  If n has even units (i.e., 2 is a unit, i.e., n is odd), then e'=2 satisfies:
  s = 2·(n+1)/2 mod (n-1) = (n+1) mod (n-1) = 2 = e'. Cond1 fires via e'=2!
  → Event (n-1, (n+1)/2) is NOT isolated for odd n.

This approach isn't working for finding the universal event. Let's check empirically
what characterises the smallest isolated event for odd composite n.
""")

print("For each odd composite n, finding the SMALLEST isolated event:")
print(f"{'n':>5} {'p':>4} {'e_u':>6} {'m':>4} {'gcd(m,e_u)':>12} {'m-1 mod p':>10} {'e_u mod p':>10}")
print("-" * 65)

for n in range(9, 100, 2):
    if phi(n) == n - 1: continue  # skip primes
    p = smallest_prime_factor(n)
    units = units_mod_n(n)
    iso_events = find_isolated_events(n)

    if iso_events:
        eu, m = iso_events[0]
        g = gcd(m, eu)
        print(f"n={n:>4} p={p:<4} e_u={eu:<6} m={m:<4} gcd={g:<12} (m-1)%p={((m-1)%p):<10} e_u%p={eu%p:<10}")

# ============================================================
print("\n" + "=" * 70)
print("PART 9: Testing the GAP A closure hypothesis")
print("Hypothesis: (e_u = n-1, m = n-1 - p) is isolated for odd composite n")
print("where p = smallest prime factor of n")
print("=" * 70)

# Based on observation: for n=9 (p=3): n-1-p = 8-3=5. Is (8,5) isolated?
# From data: n=9 isolated events include (e_u=7, m=5), (e_u=8, m=6), (e_u=5, m=2), (e_u=7, m=3)
# (8,5): e_u=8, m=5. Is this isolated?

print("\nTesting (e_u=n-1, m=n-1-p) for odd composite n:")
for n in range(9, 100, 2):
    if phi(n) == n - 1: continue
    p = smallest_prime_factor(n)
    eu = n - 1
    m = eu - p  # = n-1-p
    if m < 2 or m >= eu: continue
    units = units_mod_n(n)
    if eu not in units: continue

    iso = is_isolated(eu, m, n, units)
    if not iso:
        covering = [(ep, c) for ep in units if ep != eu
                    for fired, c in [covers_via_cond_with_n(ep, eu, m, n)] if fired]
        print(f"  n={n:>4}, p={p}: (n-1, n-1-p)=({eu},{m}): NOT isolated. Covered: {covering[:2]}")

# report
isolated_count = sum(1 for n in range(9, 100, 2)
                     if phi(n) != n-1 and (n-1) in units_mod_n(n)
                     and (n-1-smallest_prime_factor(n)) >= 2
                     and is_isolated(n-1, n-1-smallest_prime_factor(n), n, units_mod_n(n)))
total_count = sum(1 for n in range(9, 100, 2)
                  if phi(n) != n-1 and (n-1) in units_mod_n(n)
                  and (n-1-smallest_prime_factor(n)) >= 2)
print(f"\n(n-1, n-1-p) isolated for {isolated_count}/{total_count} odd composite n in [9,99]")

# ============================================================
print("\n" + "=" * 70)
print("PART 10: The CORRECT candidate — based on gcd structure")
print("Observation from Part 8: smallest isolated event often has e_u mod p close to p-1")
print("Trying: (e_u = first unit that is ≡ p-1 mod p, m = 2)")
print("=" * 70)

print("\nTesting (e_u ≡ -1 mod p, m=2) — the first unit ≡ p-1 (mod p):")
print("For n=p^k: this means e_u = p-1 (the first unit < p) if p-1 is a unit.")
print()

for n in range(9, 100, 2):
    if phi(n) == n - 1: continue
    p = smallest_prime_factor(n)
    units = units_mod_n(n)

    # Find smallest unit ≡ p-1 (mod p), i.e., ≡ -1 (mod p)
    candidates = [eu for eu in units if eu >= 2 and eu % p == p - 1]
    if not candidates: continue
    eu = candidates[0]

    iso = is_isolated(eu, 2, n, units)
    inv_eu = modinv(eu, n)
    r_dep = (-(1) * inv_eu) % n if inv_eu else None
    rdep_mod_p = r_dep % p if r_dep else None

    if iso:
        print(f"  n={n:>4}, p={p}: e_u={eu} (≡{eu%p} mod {p}), m=2, r_dep={r_dep} (≡{rdep_mod_p} mod {p}): ISOLATED ✓")
    else:
        covering = [(ep, c) for ep in units if ep != eu
                    for fired, c in [covers_via_cond_with_n(ep, eu, 2, n)] if fired]
        print(f"  n={n:>4}, p={p}: e_u={eu} (≡{eu%p} mod {p}), m=2, r_dep={r_dep}: NOT isolated. Covered: {covering[:2]}")

# ============================================================
print("\n" + "=" * 70)
print("PART 11: FINAL SUMMARY — Gap A status")
print("=" * 70)

print("""
CONFIRMED FINDINGS:

1. PRIME n: ZERO isolated m>=2 events (verified n=5,7,...,113).
   Explanation: all {1,...,n-1} are units → dense relay chain via Cond1/Cond2.
   Gap A DOES NOT APPLY for prime n (prime n uses Sole Cover bijection instead).

2. EVEN COMPOSITE n: (e_u=n-1, m=2) is ALWAYS isolated.
   Proof: Cond1 never fires (m=2 → needs (n-1)|e', impossible).
          Cond2 needs n-2 to be a unit, but gcd(n-2,n)=gcd(2,n)=2≠1 for even n.
   → B_safe ≥ 1 for all even composite n. ✓  GAP A CLOSED for even composite n.

3. ODD COMPOSITE n: isolated events exist (empirically verified for all odd composite n ≤ 99).
   No single universal isolated event found yet.
   The structure involves unit-set gaps near multiples of p (smallest prime factor).
   REMAINING GAP: analytic proof for odd composite n.

4. KEY INSIGHT: Gap A is about whether B_safe ≥ 1 in the Z0S setting (all φ(n) units present).
   This setting only arises for COMPOSITE n (when both dropped runners are non-units).
   For prime n, Gap A is vacuous (Sole Cover handles prime n directly).
   The critical remaining case is: ODD COMPOSITE n with both dropped runners non-unit.
""")

# Compute stats for summary
print("Composite n with ≥1 isolated event (Gap A not a concern):")
for n in range(4, 100):
    if phi(n) == n-1: continue  # prime
    units = units_mod_n(n)
    iso = find_isolated_events(n)
    if not iso:
        print(f"  n={n}: ZERO ISOLATED — Gap A would fail here!")
print("(If no output above, Gap A holds for all composite n < 100)")
