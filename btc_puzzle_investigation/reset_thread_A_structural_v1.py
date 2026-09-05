#!/usr/bin/env python3
"""
Reset thread A (easy / pure computation): interrogate the structural coincidence
  ord_n(2) = (n-1)/2^6
that the KNOWN_FACTS doc records but never asks "why 64 = 2^6?" of.

Questions (all exact integer arithmetic, no float):
  1. What is v_2(n-1)?  Is ord_n(2) really (n-1)/2^6 ?
  2. Is the exponent 6 the sextic 6 (= |mu_6|), or unrelated to the CM structure?
  3. Cubic/sextic residue status mod n of the curve-relevant small primes
     {2,3,5,7} -- does the sextic (6th-power) structure touch the base-10
     primes {2,5} or the curve primes {3,7}?
  4. Same for the other twist / structural constants.
No claim is a verdict; this prints facts.
"""
from ecc_secp256k1 import N_ORDER as n, P as p

# --- n-1 factorization (publicly known); verified by product below ---
NM1_FACTORS = {
    2: 6, 3: 1, 149: 1, 631: 1,
    107361793816595537: 1,
    174723607534414371449: 1,
    341948486974166000522343609283189: 1,
}

def check_factorization():
    prod = 1
    for q, e in NM1_FACTORS.items():
        prod *= q ** e
    return prod == n - 1, prod

def mult_order(a, mod, factors_of_group):
    """Exact multiplicative order of a modulo `mod`, given the factorization
    {prime: exp} of the group order (mod-1 here, mod prime)."""
    order = mod - 1
    for q in factors_of_group:
        while order % q == 0 and pow(a, order // q, mod) == 1:
            order //= q
    return order

def residue_status(a, mod, e):
    """a is an e-th power residue mod prime `mod` iff a^((mod-1)/e) == 1."""
    return pow(a, (mod - 1) // e, mod) == 1

print("=== Thread A: structural coincidence ord_n(2) = (n-1)/2^6 ===\n")
ok, prod = check_factorization()
print(f"n-1 factorization product matches n-1 : {ok}")
print(f"n-1 = {n-1}")
print(f"    = " + " * ".join(f"{q}^{e}" if e > 1 else f"{q}" for q, e in NM1_FACTORS.items()))
print()

v2 = NM1_FACTORS[2]
print(f"v_2(n-1)            = {v2}   (2-adic valuation of n-1)")
print(f"2^v2                = {2**v2}")

group_factors = list(NM1_FACTORS.keys())
ord2 = mult_order(2, n, group_factors)
idx2 = (n - 1) // ord2
print(f"ord_n(2)            = {ord2}")
print(f"index [ (Z/n)* : <2> ] = (n-1)/ord_n(2) = {idx2}")
print(f"  is that index == 2^6 = 64 ?  {idx2 == 64}")
print(f"  is that index a power of 2 ? {idx2 & (idx2-1) == 0}")
print(f"  so the '6' in 2^6 is v_2(n-1); it equals |mu_6| numerically but")
print(f"  is a 2-adic valuation, NOT a 6th-power/sextic exponent.\n")

print("=== cubic (e=3) and sextic (e=6) residue status mod n ===")
print("  (does the CM/sextic structure single out any small prime?)")
for a in (2, 3, 5, 7, 11, 13):
    is_cube = residue_status(a, n, 3)
    is_sext = residue_status(a, n, 6) if (n - 1) % 6 == 0 else None
    is_qr   = residue_status(a, n, 2)
    print(f"  a={a:>3}:  QR={is_qr!s:>5}   cube={is_cube!s:>5}   6th-power={is_sext!s:>5}")

print()
print("=== same questions for p (base field prime) ===")
# p-1 factorization is also public; verify lazily via sympy if available
try:
    from sympy import factorint
    pf = factorint(p - 1)
    print(f"v_2(p-1)            = {pf.get(2,0)}")
    ordp2 = mult_order(2, p, list(pf.keys()))
    print(f"ord_p(2)            = {ordp2}")
    print(f"index [ (Z/p)* : <2> ] = {(p-1)//ordp2}")
    print(f"  power of 2 ? {((p-1)//ordp2) & ((p-1)//ordp2 - 1) == 0}")
except Exception as e:
    print(f"(sympy factorint on p-1 unavailable/slow: {e})")
