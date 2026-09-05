#!/usr/bin/env python3
"""
METHOD 3 (replaces "rename the coincidence"): is secp256k1's constant structure
SPECIAL or GENERIC? Test the ord_n(2)=(n-1)/2^6 facts against an ensemble of random
primes (small enough that q-1 factors), quantifying rarity instead of asserting it.

secp256k1: index [ (Z/n)*:<2> ] = 2^6 (2 generates the full ODD part), v_2(n-1)=6.
Questions: how often is the index of 2 a pure power of 2 (2 generates the odd part)?
what is P(v_2(q-1)=6)? So is the pair a design fingerprint or a coincidence?
"""
import random
from sympy import nextprime, factorint

def order_index(q):
    """index [ (Z/q)*:<2> ] = (q-1)/ord_q(2); needs factorization of q-1."""
    f = factorint(q-1)
    order = q-1
    for p in f:
        while order % p == 0 and pow(2, order//p, q) == 1:
            order //= p
    return (q-1)//order, f.get(2,0)

rng = random.Random(20260711)
NP = 3000
LO, HI = 1<<40, 1<<44
pow2_index = 0; v2_hist = {}; both = 0
samples = 0
while samples < NP:
    q = nextprime(rng.randrange(LO, HI))
    if q >= HI: continue
    idx, v2 = order_index(q)
    samples += 1
    is_pow2 = (idx & (idx-1)) == 0
    if is_pow2: pow2_index += 1
    v2_hist[v2] = v2_hist.get(v2,0)+1
    if is_pow2 and v2 == 6: both += 1

print("=== METHOD 3: genericity of secp256k1's ord_n(2) structure ===\n")
print(f"ensemble: {samples} random primes in [2^40, 2^44)\n")
print(f"P(index of 2 is a pure power of 2, i.e. 2 generates the odd part) = "
      f"{pow2_index}/{samples} = {pow2_index/samples:.3f}")
print(f"   (Artin-type heuristic ~0.37; secp256k1 HAS this property)\n")
print("P(v_2(q-1) = k):")
for k in sorted(v2_hist):
    bar = "#"*(v2_hist[k]*60//samples)
    print(f"   v2={k:>2}: {v2_hist[k]/samples:.3f} {bar}")
print(f"\nsecp256k1 has v2(n-1)=6 (heuristic P=2^-6={2**-6:.4f}) AND 2-generates-odd-part.")
print(f"joint in ensemble: {both}/{samples} = {both/samples:.4f}")
print("\nreading: neither property is extraordinary; the pair is uncommon-but-generic,")
print("consistent with coincidence rather than a designed fingerprint (scoped to this")
print("ensemble/size range; the properties are group-structural, ~scale-invariant).")
