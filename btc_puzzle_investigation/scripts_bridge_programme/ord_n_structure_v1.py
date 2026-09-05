#!/usr/bin/env python3
"""PREREG_ord_n_structure_v1 -- exact integers only, no floats in the signal path."""
import random

p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def is_prime(m, rounds=40):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d, s = m-1, 0
    while d % 2 == 0: d //= 2; s += 1
    rnd = random.Random(12345)
    for _ in range(rounds):
        a = rnd.randrange(2, m-1)
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

# --- Q1: factorization of n-1, verified in-script (NOT inherited on trust) -----
CAND = [2]*6 + [3, 149, 631, 107361793816595537, 174723607534414371449,
                341948486974166000522343609283189]
prod = 1
for f in CAND: prod *= f
print("=== Q1: factorization of n-1 ===")
print("n-1 =", n-1)
print("product of asserted factors == n-1 :", prod == (n-1))
if prod != (n-1):
    print("!! asserted factorization WRONG; residual =", (n-1)//prod if (n-1) % prod == 0 else "not a divisor")
    raise SystemExit("factorization failed -- record is wrong")
for f in sorted(set(CAND)):
    print(f"   factor {f}  prime? {is_prime(f)}")
print("n prime?", is_prime(n), " p prime?", is_prime(p))

def val(m, q):
    v = 0
    while m % q == 0: m //= q; v += 1
    return v
print("nu_2(n-1) =", val(n-1, 2), "   nu_3(n-1) =", val(n-1, 3))

PF = sorted(set(CAND))

def order(b, mod=n):
    """multiplicative order of b mod n, by descending from n-1 through prime factors"""
    assert pow(b, mod-1, mod) == 1
    o = mod-1
    for q in PF:
        while o % q == 0 and pow(b, o//q, mod) == 1:
            o //= q
    return o

# --- Q2 / Q3 -----------------------------------------------------------------
print("\n=== Q2/Q3: the two claimed orders ===")
for name, b in (("2", 2), ("p mod n", p % n)):
    o = order(b)
    c = (n-1)//o
    print(f"  base {name:>8}:  cofactor (n-1)/ord = {c}     [ord = (n-1)/{c}]")
    print(f"             ord = {o}")

c2 = (n-1)//order(2)
cp = (n-1)//order(p % n)
print(f"\n  record claims: c_2 = 64 -> got {c2}   {'MATCH' if c2==64 else '*** MISMATCH ***'}")
print(f"  record claims: c_p =  6 -> got {cp}   {'MATCH' if cp==6 else '*** MISMATCH ***'}")

# --- Q4: forced identity self-test -------------------------------------------
t = p + 1 - n
print("\n=== Q4: trace self-test ===")
print("  t = p+1-n =", t, f"({t.bit_length()} bits)")
print("  p == t-1 mod n :", (p - (t-1)) % n == 0)
print("  |t| <= 2*sqrt(p) :", t*t <= 4*p)
print("  n mod 3 =", n % 3, "  n mod 4 =", n % 4, "  n mod 8 =", n % 8, "  n mod 12 =", n % 12)
print("  p mod 3 =", p % 3, "  p mod 4 =", p % 4, "  p mod 8 =", p % 8, "  p mod 12 =", p % 12)

# --- Q5: which subgroup: power-residue character at each prime l | n-1 --------
print("\n=== Q5: power-residue characters (1 = is an l-th power) ===")
print(f"  {'l':>34}  2 is l-th pow?   p is l-th pow?")
for q in PF:
    r2 = pow(2, (n-1)//q, n) == 1
    rp = pow(p % n, (n-1)//q, n) == 1
    print(f"  {q:>34}       {str(r2):>5}            {str(rp):>5}")

# --- C1: THE CONTROL ROW -----------------------------------------------------
print("\n=== C1: CONTROL -- cofactor distribution over all primes q < 1000 ===")
sieve = [True]*1000; sieve[0]=sieve[1]=False
for i in range(2, 32):
    if sieve[i]:
        for j in range(i*i, 1000, i): sieve[j] = False
small = [i for i in range(1000) if sieve[i]]
cof = {}
for q in small:
    cof[q] = (n-1)//order(q)
from collections import Counter
dist = Counter(cof.values())
print(f"  bases tested: {len(small)} primes < 1000")
print("  cofactor -> how many bases:")
for c, k in sorted(dist.items()):
    ex = [str(q) for q in small if cof[q] == c]
    shown = ", ".join(ex[:14]) + (f", ... (+{len(ex)-14})" if len(ex) > 14 else "")
    print(f"    c = {c:>4} : {k:>3}   [{shown}]")

hit64 = [q for q in small if cof[q] % 64 == 0]
hit6  = [q for q in small if cof[q] % 6 == 0]
print(f"\n  #(64 | c_q) = {len(hit64)}   (expected ~ {len(small)}/64 = {len(small)/64:.2f})   bases: {hit64}")
print(f"  #( 6 | c_q) = {len(hit6)}   (expected ~ {len(small)}/6 = {len(small)/6:.2f})")
print(f"  is 2 unique with 64 | c ? {hit64 == [2]}")
print(f"  #(c_q == 1, i.e. primitive roots) = {dist.get(1,0)}")

# odd order == being a 2^6-th power residue (since nu_2(n-1)=6)
oddord = [q for q in small if order(q) % 2 == 1]
print(f"  #(odd order = is a 2^6-th power residue) = {len(oddord)}  bases: {oddord}")
