#!/usr/bin/env python3
"""
Test the idea: is the amicable pair (p,n) a "spectral fixed point" of P_m -- do p and
n share the survival core / spectral ceiling BECAUSE of amicability, or just because
both are primes =1 mod 3?

The whole test is the CONTROL. Two near-tautological readings ruled out first:
  - mu6 = units of Z[omega] = the SAME 6 ring elements always -> "shared mu6 core" is
    trivial for anything over Z[omega]. No content.
  - large-sieve ceiling ~ phi(m)=m-1 ~ m for any large prime -> matches at scale for
    ANY two primes. No content.
The only NON-tautological claims, tested here with random-prime controls:
  (A) does amicability PRESERVE the split-in-Z[omega] regime (m=1 mod3, where mu6
      applies)? i.e. is the amicable n ALWAYS =1 mod3? (random prime: ~1/2). If yes,
      that is an amicable-specific "fixed point of the survival-core class."
  (B) fine spectral ceiling depends on m-1's factorization. Do (q-1) and (r-1) of an
      amicable pair share fine structure BEYOND what random prime pairs share (both
      have 2,3 | m-1 generically since m=1 mod6)? gcd(q-1,r-1) amicable vs random.
Method: small amicable pairs (q,r) for y^2=x^3+b by exact point counting; controls =
random primes of matched size/class. Exact integers.
"""
import random
from sympy import isprime, factorint, primerange
from math import gcd


def legendre(a, p):
    a %= p
    if a == 0: return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def order_Eb(q, b):
    b %= q
    cnt = 1  # infinity
    for x in range(q):
        cnt += 1 + legendre((x * x % q * x + b) % q, q)
    return cnt


def find_amicable(qmax=400, bs=(1, 2, 3, 5, 7), allow_inert=False):
    pairs = []
    seen = set()
    for q in primerange(7, qmax):
        if q % 3 != 1 and not allow_inert:
            continue
        for b in bs:
            if b % q == 0: continue
            r = order_Eb(q, b)
            if r != q and isprime(r) and r > 3:
                # amicable if E_b over F_r has order q
                if order_Eb(r, b) == q:
                    key = tuple(sorted((q, r)))
                    if key not in seen:
                        seen.add(key)
                        pairs.append((q, r, b))
    return pairs


def m_minus_1_profile(m):
    f = factorint(m - 1)
    return {"v2": f.get(2, 0), "v3": f.get(3, 0), "omega": len(f),
            "rad": [p for p in f]}


def main():
    print("Generating small amicable pairs (q,r) for y^2=x^3+b, ALL q (incl. q=2 mod3) ...")
    pairs = find_amicable(2000, allow_inert=True)
    print(f"  found {len(pairs)} amicable pairs\n")
    for q, r, b in pairs[:20]:
        print(f"    (q={q}, r={r}, b={b})  q%3={q%3} r%3={r%3}")
    n_inert_member = sum(1 for q, r, b in pairs if q % 3 == 2 or r % 3 == 2)
    print(f"  ... ({len(pairs)} total)  pairs with ANY member =2 mod3 (inert/supersingular): "
          f"{n_inert_member}")

    # (A) split preservation: is r ALWAYS =1 mod 3 (given q=1 mod 3)?
    print("\n(A) SURVIVAL-CORE PRESERVATION (does amicability keep m=1 mod3 / mu6 regime?)")
    both1 = sum(1 for q, r, b in pairs if q % 3 == 1 and r % 3 == 1)
    r1 = sum(1 for q, r, b in pairs if r % 3 == 1)
    print(f"    amicable pairs with r=1 mod3: {r1}/{len(pairs)}   both=1 mod3: {both1}/{len(pairs)}")
    print(f"    CONTROL: a random prime of that size is =1 mod3 with prob ~1/2.")
    print(f"    => {'PRESERVED (amicable-specific: r forced =1 mod3, mu6 core kept)' if r1==len(pairs) else 'NOT always preserved'}")

    # (B) fine ceiling: do (q-1),(r-1) share fine structure beyond generic 2,3 | m-1?
    print("\n(B) FINE SPECTRAL CEILING (m-1 structure): amicable vs random-prime pairs")
    # amicable: gcd(q-1,r-1) and its radical beyond {2,3}
    def extra_shared(a, b):
        g = gcd(a - 1, b - 1)
        return sorted(p for p in factorint(g) if p > 3)  # shared primes beyond 2,3
    am_extra = [extra_shared(q, r) for q, r, b in pairs]
    print(f"    amicable pairs sharing a prime >3 in gcd(q-1,r-1): "
          f"{sum(1 for e in am_extra if e)}/{len(pairs)}  (examples: {[e for e in am_extra if e][:5]})")
    # random control: pairs of random primes =1 mod3 of similar size
    rng = random.Random(1)
    smallish = [q for q in primerange(7, 2000) if q % 3 == 1]
    rc = 0; RT = 2000
    for _ in range(RT):
        a, b2 = rng.choice(smallish), rng.choice(smallish)
        if a != b2 and extra_shared(a, b2): rc += 1
    print(f"    CONTROL random =1mod3 prime pairs sharing a prime>3 in gcd(m-1): "
          f"{rc}/{RT} = {rc/RT:.3f}")
    amfrac = sum(1 for e in am_extra if e) / len(pairs) if pairs else 0
    print(f"    amicable frac {amfrac:.3f} vs control {rc/RT:.3f} => "
          f"{'amicable-SPECIFIC fine sharing' if amfrac > rc/RT + 0.2 else 'NOT amicable-specific (same as generic primes) -- fine ceiling NOT a fixed point'}")

    print("\n(C) survival-core SIZE (mu6 modes) per member:")
    print("    for any m=1 mod3 (split): (Z[omega]/pi_m)* survives to |mu6|=6 modes;")
    print("    m=2 mod3 (inert): mu2-shadow. This is a property of m mod 3, identical")
    print("    for BOTH members iff (A) holds -- it is the 'shared core', but its")
    print("    content is exactly (A): amicability staying in the split regime.")


if __name__ == "__main__":
    main()
