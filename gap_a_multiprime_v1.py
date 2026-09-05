"""
gap_a_multiprime_v1.py
======================
Investigation of Gap A for odd composite n with MULTIPLE PRIME FACTORS.

Goal: Find the constructive witness (eu, m=2) for n = p1^a1 * p2^a2 * ...

KNOWN:
  (eu, m=2) isolated iff gcd(e'*, n) > 1, where
    e'* = n-2a      if 2a ≤ eu  (Case 1)
    e'* = n+eu-2a   if 2a > eu  (Case 2, excluding 2a=eu+1)
  a = n mod eu.

  Isolation criterion (by prime r | n):
    Case 1: r | floor(n/eu)  (equivalent to r | a, since r|n and a = n-eu*q)
    Case 2: r | (1 + 2*q)    where q = floor(n/eu)
      ↔ q ≡ (r-1)/2 (mod r)

  For ANY prime r | n, this gives isolation.

STRATEGY:
  Part A: For each odd composite n with ≥2 prime factors, find the SMALLEST
          isolated eu and characterize its structure.
  Part B: For n=p*q (semiprime), map the isolation resonances q≡0 and q≡(r-1)/2.
          Show the resonance intervals always contain a unit.
  Part C: The (r-1)/2 resonance for each prime r|n. Show constructive witness.
  Part D: Tightest cases — when is only ONE eu isolated? What's special?
  Part E: Prove the interval always contains a unit via CRT / density argument.
"""

from math import gcd
from itertools import combinations

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

def prime_factors(n):
    factors = []
    d, temp = 2, n
    while d*d <= temp:
        if temp%d==0:
            factors.append(d)
            while temp%d==0: temp//=d
        d+=1
    if temp>1: factors.append(temp)
    return factors

def factorization(n):
    fac = {}
    d = 2
    while d*d <= n:
        while n%d==0:
            fac[d] = fac.get(d,0)+1
            n//=d
        d+=1
    if n>1: fac[n] = fac.get(n,0)+1
    return fac

def smallest_prime(n):
    for p in range(2, n):
        if n%p==0: return p
    return n

def compute_estar(eu, n):
    a = n % eu
    two_a = 2*a
    if two_a <= eu:
        estar = n - two_a
    else:
        estar = n + eu - two_a
    return estar, gcd(estar, n)

def is_isolated(eu, n):
    estar, g = compute_estar(eu, n)
    return g > 1

def is_multiprime(n):
    return len(prime_factors(n)) >= 2


# ============================================================
print("=" * 70)
print("PART A: Smallest isolated eu for each odd composite n with ≥2 prime factors")
print("  Focus: n=p*q (semiprime), n=p^2*q, n=p*q*r (3 factors)")
print("=" * 70)

print("\nSemiprime n=p*q (p<q both prime), n ≤ 200:")
print(f"{'n':>5} {'p':>4} {'q':>4} | {'min_eu':>7} {'a':>5} {'q_floor':>8} "
      f"{'case':>5} {'e*':>6} {'gcd':>5} | {'via_r':>6} {'resonance':>12} {'iso_total':>10}")
print("-" * 85)

for n in range(9, 201, 2):
    if phi(n) == n-1: continue
    pf = prime_factors(n)
    if len(pf) != 2: continue
    p, q = pf[0], pf[1]
    if p == q: continue  # skip p^2
    units = units_mod_n(n)
    all_units_ge3 = [eu for eu in units if eu >= 3]

    # Find smallest isolated eu
    min_eu = None
    for eu in sorted(all_units_ge3):
        if is_isolated(eu, n):
            min_eu = eu
            break

    if min_eu is None:
        print(f"n={n:>4} p={p:<3} q={q:<4} | NO ISOLATED EU FOUND!")
        continue

    a = n % min_eu
    qfl = n // min_eu
    estar, g = compute_estar(min_eu, n)
    two_a = 2*a
    case = 'C1' if two_a <= min_eu else 'C2'
    # Which prime r divides e'*?
    via_r = [r for r in pf if g % r == 0]
    # Which resonance?
    if case == 'C1':
        res = f"q≡0 mod {via_r[0] if via_r else '?'}"
    else:
        res = f"q≡{(via_r[0]-1)//2 if via_r else '?'} mod {via_r[0] if via_r else '?'}"

    total_iso = sum(1 for eu in all_units_ge3 if is_isolated(eu, n))
    print(f"n={n:>4} p={p:<3} q={q:<4} | eu={min_eu:>5} a={a:>4} qfl={qfl:>6} "
          f"{case:>5} e*={estar:>5} g={g:>3} | r={via_r} {res:>12} iso={total_iso:>8}")


# ============================================================
print("\n" + "=" * 70)
print("PART B: Resonance analysis for semiprimes n=p*q")
print("  For each prime r|n, find intervals where floor(n/eu) ≡ (r-1)/2 (mod r)")
print("  and check if they contain a unit.")
print("=" * 70)

def resonance_intervals(n, r, mode='half'):
    """Find all k with k ≡ target (mod r) and k ≥ 1 and n/(k+1) < n/k (non-empty interval)."""
    target = 0 if mode == 'zero' else (r-1)//2
    results = []
    k = target if target > 0 else r
    while k <= n:
        lo = n / (k+1)
        hi = n / k
        width = hi - lo
        # integers in open interval (lo, hi)
        ints_in = list(range(int(lo)+1, int(hi)+1))
        # filter to units of n
        units_in = [eu for eu in ints_in if gcd(eu, n) == 1 and eu >= 3]
        if ints_in:
            results.append((k, lo, hi, width, ints_in, units_in))
        k += r
    return results

print("\nFor n=15 (p=3, q=5): resonance intervals for r=3 (target q≡1 mod 3):")
n=15
for r in [3,5]:
    target = (r-1)//2
    print(f"  r={r}, target q≡{target} (mod {r}):")
    intervals = resonance_intervals(n, r, mode='half')
    for k, lo, hi, w, ints_in, units_in in intervals[:6]:
        print(f"    k={k:>3}: interval ({lo:.2f}, {hi:.2f}), width={w:.3f}, ints={ints_in}, units={units_in}")

print("\nFor n=35 (p=5, q=7): resonance intervals for r=5 and r=7:")
n=35
for r in [5,7]:
    target = (r-1)//2
    print(f"  r={r}, target q≡{target} (mod {r}):")
    intervals = resonance_intervals(n, r, mode='half')
    for k, lo, hi, w, ints_in, units_in in intervals[:6]:
        print(f"    k={k:>3}: interval ({lo:.2f}, {hi:.2f}), width={w:.3f}, ints={ints_in}, units={units_in}")

print("\nFor n=77 (p=7, q=11): resonance intervals for r=7 and r=11:")
n=77
for r in [7,11]:
    target = (r-1)//2
    print(f"  r={r}, target q≡{target} (mod {r}):")
    intervals = resonance_intervals(n, r, mode='half')
    for k, lo, hi, w, ints_in, units_in in intervals[:6]:
        print(f"    k={k:>3}: interval ({lo:.2f}, {hi:.2f}), width={w:.3f}, ints={ints_in}, units={units_in}")


# ============================================================
print("\n" + "=" * 70)
print("PART C: For n=p*q, constructive witness via the (r-1)/2 resonance")
print("  Claim: eu = 2*q - 1 (analog of n=p^2 formula but with LARGER prime q)")
print("=" * 70)

print("\nTesting eu = 2*min(p,q) - 1 and eu = 2*max(p,q) - 1 for semiprimes:")
print(f"{'n':>5} {'p':>4} {'q':>5} | {'eu_2p-1':>8} {'iso?':>6} | {'eu_2q-1':>8} {'iso?':>6} | {'eu_q-1':>7} {'iso?':>6} | {'eu_p-1':>7} {'iso?':>6}")
print("-" * 75)

for n in range(9, 101, 2):
    if phi(n) == n-1: continue
    pf = prime_factors(n)
    if len(pf) != 2: continue
    p, q = pf[0], pf[1]
    if p == q: continue

    def check_eu(eu, n):
        if eu < 3 or eu >= n or gcd(eu, n) != 1: return 'N/A (non-unit)'
        estar, g = compute_estar(eu, n)
        return f'YES(gcd={g})' if g > 1 else 'no'

    r1 = check_eu(2*p-1, n)
    r2 = check_eu(2*q-1, n)
    r3 = check_eu(q-1, n)
    r4 = check_eu(p-1, n)
    print(f"n={n:>4} p={p:<3} q={q:<4} | eu={2*p-1:>5}  {r1:>12} | eu={2*q-1:>5}  {r2:>12} | eu={q-1:>5}  {r3:>12} | eu={p-1:>5}  {r4:>12}")


# ============================================================
print("\n" + "=" * 70)
print("PART D: Universal formula search — what do the isolated eu values have in common?")
print("  For each semiprime, look at ALL isolated eu and their arithmetic.")
print("=" * 70)

print("\nn=p*q semiprimes: structure of isolated eu values")
for n in [15, 21, 35, 55, 77, 91, 143, 187]:
    pf = prime_factors(n)
    p, q = pf[0], pf[1]
    units = units_mod_n(n)
    all_units_ge3 = [eu for eu in units if eu >= 3]
    iso_events = [(eu, n%eu, n//eu, compute_estar(eu,n))
                  for eu in all_units_ge3 if is_isolated(eu, n)]
    print(f"\nn={n} (p={p}, q={q}):")
    print(f"  {'eu':>5} {'a=n%eu':>8} {'q=n//eu':>9} {'e*':>6} {'gcd':>5} {'case':>5} "
          f"{'eu mod p':>9} {'eu mod q':>9} {'a mod p':>8} {'a mod q':>8} {'via_r':>6}")
    for eu, a, qfl, (estar, g) in iso_events[:12]:
        two_a = 2*a
        case = 'C1' if two_a <= eu else 'C2'
        via = [r for r in [p,q] if g%r==0]
        print(f"  {eu:>5} {a:>8} {qfl:>9} {estar:>6} {g:>5} {case:>5} "
              f"{eu%p:>9} {eu%q:>9} {a%p:>8} {a%q:>8} {via}")


# ============================================================
print("\n" + "=" * 70)
print("PART E: The q ≡ (r-1)/2 resonance — does it always contain a unit?")
print("  For n=p*q semiprime, smallest prime p, resonance at k=(p-1)/2 (mod p).")
print("  Take k=(p-1)/2 (smallest positive resonance value for r=p).")
print("  Interval: (n/(k+1), n/k) = (pq/((p+1)/2), pq/((p-1)/2)) = (2pq/(p+1), 2q).")
print("  Width = 2q - 2pq/(p+1) = 2q/(p+1).")
print("=" * 70)

print("\nFor semiprimes n=p*q, interval for k=(p-1)/2 resonance via r=p:")
print(f"{'n':>5} {'p':>4} {'q':>5} | {'k':>4} {'lo':>8} {'hi':>8} {'width':>8} | {'units_in_interval':>30} | {'iso_confirmed':>14}")
print("-" * 90)

for n in range(9, 201, 2):
    if phi(n) == n-1: continue
    pf = prime_factors(n)
    if len(pf) != 2: continue
    p, q = pf[0], pf[1]
    if p == q: continue

    k = (p-1)//2  # target floor value: k ≡ (p-1)/2 (mod p)
    if k == 0: k = p  # for p=3: (p-1)/2=1, first resonance k=1

    lo = n / (k+1)
    hi = n / k
    width = hi - lo
    ints_in = list(range(int(lo)+1, int(hi)+1))
    units_in = [eu for eu in ints_in if gcd(eu, n) == 1 and eu >= 3]
    iso_confirmed = [eu for eu in units_in if is_isolated(eu, n)]

    has_unit = len(units_in) > 0
    flag = '' if has_unit else '*** NO UNIT ***'
    print(f"n={n:>4} p={p:<3} q={q:<4} | k={k:>3} ({lo:>6.2f},{hi:>6.2f}) w={width:>6.2f} | "
          f"units={str(units_in):<28} | iso={iso_confirmed} {flag}")


# ============================================================
print("\n" + "=" * 70)
print("PART F: CRT / density argument — why does the resonance interval ALWAYS contain a unit?")
print("  For n=p*q, interval (2pq/(p+1), 2q) has width 2q/(p+1).")
print("  Non-units in this interval: multiples of p or q.")
print("  Multiples of q in (2pq/(p+1), 2q): q·j with j in (2p/(p+1), 2) → only j=1 possible?")
print("  But q·1 = q ≤ 2q is in the interval only if q > 2pq/(p+1), i.e., (p+1)>2p, i.e., p<1. No!")
print("  So NO multiples of q are in (2pq/(p+1), 2q) for p ≥ 2!")
print("  Multiples of p in interval: p·j with j in (2q/(p+1), 2q/p).")
print("  Width of j-interval: 2q/p - 2q/(p+1) = 2q/(p(p+1)).")
print("=" * 70)

print("\nVerification: are there ALWAYS non-multiples-of-q in the interval?")
print("(Equivalently: is the interval non-empty of integers coprime to q?)")
for n in [15, 21, 35, 55, 77, 91, 143, 187, 209, 221, 247, 299]:
    pf = prime_factors(n)
    if len(pf) != 2: continue
    p, q = pf[0], pf[1]
    if p == q: continue
    k = (p-1)//2
    if k == 0: k = p
    lo, hi = n/(k+1), n/k
    ints_in = list(range(int(lo)+1, int(hi)+1))
    mult_q = [x for x in ints_in if x % q == 0]
    mult_p = [x for x in ints_in if x % p == 0]
    non_q = [x for x in ints_in if x % q != 0]
    units_in = [x for x in ints_in if gcd(x, n) == 1 and x >= 3]
    print(f"n={n:>4} (p={p},q={q}): k={k}, interval=({lo:.2f},{hi:.2f}), "
          f"ints={ints_in}, mult_q={mult_q}, mult_p={mult_p}, units={units_in}")

# ============================================================
print("\n" + "=" * 70)
print("PART G: n=p^a*q type (mixed prime power and distinct prime)")
print("  E.g. n=45=3^2*5, n=63=3^2*7, n=75=3*5^2, etc.")
print("=" * 70)

print("\nn=p^a*q with multiple distinct prime factors:")
print(f"{'n':>5} {'factorization':>15} | {'min_eu':>7} {'e*':>6} {'gcd':>5} {'case':>5} {'via_r':>8} | {'iso_total':>10}")
print("-" * 65)
for n in range(9, 201, 2):
    if phi(n) == n-1: continue
    pf = prime_factors(n)
    if len(pf) < 2: continue
    fac = factorization(n)
    fac_str = '·'.join(f'{p}^{k}' if k>1 else str(p) for p,k in sorted(fac.items()))
    units = units_mod_n(n)
    all_units_ge3 = [eu for eu in units if eu >= 3]
    min_eu = next((eu for eu in sorted(all_units_ge3) if is_isolated(eu, n)), None)
    if min_eu is None:
        print(f"n={n:>4} ({fac_str:>13}) | NO ISOLATED EU!")
        continue
    estar, g = compute_estar(min_eu, n)
    a = n % min_eu
    case = 'C1' if 2*a <= min_eu else 'C2'
    via_r = [r for r in pf if g % r == 0]
    total = sum(1 for eu in all_units_ge3 if is_isolated(eu, n))
    print(f"n={n:>4} ({fac_str:>13}) | eu={min_eu:>5} e*={estar:>5} g={g:>4} {case:>5} r={via_r} | iso={total:>8}")


# ============================================================
print("\n" + "=" * 70)
print("PART H: The 3-prime-factor cases — n=p*q*r")
print("=" * 70)

three_prime_n = []
for n in range(9, 500, 2):
    if phi(n) == n-1: continue
    pf = prime_factors(n)
    if len(pf) == 3:
        three_prime_n.append((n, pf))

print(f"\nn=p*q*r (three distinct odd prime factors), first 20:")
print(f"{'n':>6} {'primes':>15} | {'min_eu':>7} {'case':>5} {'via_r':>10} | {'iso_total':>10}")
print("-" * 60)
for n, pf in three_prime_n[:20]:
    units = units_mod_n(n)
    all_units_ge3 = [eu for eu in units if eu >= 3]
    min_eu = next((eu for eu in sorted(all_units_ge3) if is_isolated(eu, n)), None)
    if min_eu is None:
        print(f"n={n:>5} {str(pf):>15} | NO ISOLATED EU!")
        continue
    estar, g = compute_estar(min_eu, n)
    a = n % min_eu
    case = 'C1' if 2*a <= min_eu else 'C2'
    via_r = [r for r in pf if g % r == 0]
    total = sum(1 for eu in all_units_ge3 if is_isolated(eu, n))
    print(f"n={n:>5} {str(pf):>15} | eu={min_eu:>5} {case:>5} r={via_r} | iso={total:>8}")


# ============================================================
print("\n" + "=" * 70)
print("PART I: KEY QUESTION — for n=p*q semiprime, does eu=q+p-2 always work?")
print("  (Generalizing eu=2p-1 from n=p^2 to n=p*q)")
print("=" * 70)

print("\nTesting candidate universal formulas for semiprimes n=p*q:")
candidates = [
    ('q+p-2', lambda p,q,n: q+p-2),
    ('q-p', lambda p,q,n: q-p),
    ('q-p+1', lambda p,q,n: q-p+1),
    ('(q-1)//p * p + (p-1)', lambda p,q,n: (q-1)//p * p + p-1),  # residue trick
    ('n//(p+1)+1', lambda p,q,n: n//(p+1)+1),
    ('2*p-1 for p=smallest', lambda p,q,n: 2*p-1),
    ('p+q-2', lambda p,q,n: p+q-2),
]

print(f"\n{'candidate':>25} | success rate | n where it fails")
print("-" * 70)
for cname, cfunc in candidates:
    successes = 0
    failures = []
    total_tested = 0
    for n in range(9, 201, 2):
        if phi(n) == n-1: continue
        pf = prime_factors(n)
        if len(pf) != 2: continue
        p, q = pf[0], pf[1]
        if p == q: continue
        total_tested += 1
        try:
            eu = cfunc(p, q, n)
        except:
            failures.append(n)
            continue
        if eu < 3 or eu >= n or gcd(eu, n) != 1:
            failures.append(n)
            continue
        if is_isolated(eu, n):
            successes += 1
        else:
            failures.append(n)
    print(f"{cname:>25} | {successes}/{total_tested}  | {failures[:10]}")
