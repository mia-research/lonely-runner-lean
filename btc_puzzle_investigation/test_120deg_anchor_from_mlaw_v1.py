#!/usr/bin/env python3
"""
test_120deg_anchor_from_mlaw_v1.py  --  2026-07-30

Tests the four-step chain proposed for the anchor cell:
  (1) m = 1 at secp (7 a cubic non-residue)
  (2) z^4 + m z^2 + 1 factors at m=1 as (z^2+z+1)(z^2-z+1)
  (3) eigenvalues = sqrt(p) * {w, w^2, -w, -w^2}, and "the ratio of the +/- pairs is zeta_3"
  (4) => the 120-degree law holds at the 2^256 scale

EXACT ARITHMETIC ONLY.  No float anywhere.  Roots of unity are represented by their
exponent in Z/24 (every root of z^4+m z^2+1 for m in {-2,-1,0,1,2} is a 24th root of
unity); membership is DERIVED from the defining polynomial by exact reduction in
Z[x]/(Phi_24) = Z[x]/(x^8 - x^4 + 1), never asserted from a paste.

zeta_3 = zeta_24^8.
"""
from fractions import Fraction

N = 24
PHI24 = [1, 0, 0, 0, -1, 0, 0, 0, 1]  # x^8 - x^4 + 1, low-degree-first


# ---------- exact arithmetic in Z[x]/(Phi_24) ----------
def reduce_phi24(c):
    """Reduce an integer coeff list (low-first) modulo x^8 - x^4 + 1, i.e. x^8 = x^4 - 1."""
    c = list(c)
    while len(c) > 8:
        top = c.pop()
        d = len(c)  # exponent of the removed term
        k = d - 8
        c[k + 4] = c[k + 4] + top   # x^(k+8) = x^(k+4) - x^k
        c[k] = c[k] - top
    while len(c) < 8:
        c.append(0)
    return c


def zeta_pow(e):
    """zeta_24^e as an element of Z[x]/(Phi_24)."""
    e %= N
    c = [0] * (e + 1)
    c[e] = 1
    return reduce_phi24(c)


def is_root(m, e):
    """Exact test: is zeta_24^e a root of z^4 + m z^2 + 1 ?"""
    v4, v2 = zeta_pow(4 * e), zeta_pow(2 * e)
    tot = [v4[i] + m * v2[i] for i in range(8)]
    tot[0] += 1
    return all(t == 0 for t in tot)


def roots_of(m):
    return [e for e in range(N) if is_root(m, e)]


# ---------- the N1 route's own statistic ----------
def order_in_mu(e):
    g = 1
    while (e * g) % N != 0:
        g += 1
    return N // __import__("math").gcd(N, e) if e else 1


def zeta3_ratio_pairs(exps):
    """Ordered pairs (i,j) of the eigenvalue multiset with alpha_j / alpha_i = zeta_3.

    This is exactly g = deg gcd(L*(T), L*(zeta_3 T)) : the count of ordered pairs whose
    ratio is a primitive cube root of unity.  Multiplicity-aware.
    """
    out = []
    for i, a in enumerate(exps):
        for j, b in enumerate(exps):
            if (b - a) % N == 8:
                out.append((i, j))
    return out


def label(e):
    """Human label for zeta_24^e."""
    from math import gcd
    o = N // gcd(N, e) if e else 1
    return f"zeta_24^{e:<2d} (order {o:>2d})"


# ---------- multiplicity: the char poly z^4+mz^2+1 can have repeated roots ----------
def multiset(m):
    """Root multiset of z^4 + m z^2 + 1 with multiplicity, as Z/24 exponents."""
    simple = roots_of(m)
    if len(simple) == 4:
        return simple
    # z^4+mz^2+1 = (z^2 - r1)(z^2 - r2) with r1 r2 = 1, r1 + r2 = -m.
    # discriminant m^2 - 4 == 0  <=>  m = +/-2  =>  each of the two roots is doubled.
    assert m in (-2, 2) and len(simple) == 2, (m, simple)
    return sorted(simple * 2)


print("=" * 78)
print("T1/T2  root systems DERIVED from z^4 + m z^2 + 1 by exact reduction in Z[x]/Phi_24")
print("=" * 78)
results = {}
for m in (-2, -1, 0, 1, 2):
    ms = multiset(m)
    pairs = zeta3_ratio_pairs(ms)
    results[m] = (ms, pairs)
    print(f"\nm = {m:+d}   roots (x sqrt(p)):")
    for e in ms:
        print(f"      {label(e)}")
    print(f"   g = #ordered pairs with ratio zeta_3  =  {len(pairs)}"
          f"   {'<-- 120 deg law HOLDS' if len(pairs) == 2 else ''}")
    for (i, j) in pairs:
        print(f"      alpha[{j}]/alpha[{i}] = zeta_3 :  {label(ms[j])} / {label(ms[i])}")

print()
print("=" * 78)
print("T2b  the paste's item 3 as literally written: 'ratio of the +/- eigenvalue pairs'")
print("=" * 78)
# m=1 set as the paste names it: {w, w^2, -w, -w^2}
w, w2 = 8, 16                     # zeta_3, zeta_3^2
mw, mw2 = (8 + 12) % 24, (16 + 12) % 24   # -w, -w^2
named = {"w": w, "w^2": w2, "-w": mw, "-w^2": mw2}
print(f"   paste's multiset  = {{{', '.join(f'{k}={label(v)}' for k, v in named.items())}}}")
print(f"   derived m=1 multiset = {sorted(results[1][0])}  "
      f"vs paste {sorted(named.values())}  ->  "
      f"{'SAME SET' if sorted(results[1][0]) == sorted(named.values()) else 'DIFFERENT'}")
print()
print("   every ordered ratio in the m=1 multiset:")
for ka, va in named.items():
    for kb, vb in named.items():
        if ka == kb:
            continue
        d = (vb - va) % N
        tag = "  == zeta_3  (120 deg)" if d == 8 else ("  == zeta_3^2 (240 deg)" if d == 16 else "")
        print(f"      {kb:>4s} / {ka:<4s} = {label(d)}{tag}")
print()
print("   the two '+/- pairs' are (w, -w) and (w^2, -w^2):")
for a, b in (("w", "-w"), ("w^2", "-w^2")):
    d = (named[b] - named[a]) % N
    print(f"      {b:>4s} / {a:<4s} = {label(d)}   -> ratio is "
          f"{'zeta_3' if d == 8 else 'NOT zeta_3'}")

print()
print("=" * 78)
print("T3  CONTROL: does g=2 discriminate m=1, i.e. is the cubic-residue step load-bearing?")
print("=" * 78)
for m in (-2, -1, 0, 1, 2):
    ms, pairs = results[m]
    print(f"   m = {m:+d}  ->  g = {len(pairs)}")
g2 = [m for m in results if len(results[m][1]) == 2]
print(f"\n   g = 2 exactly for m in {g2}")
print(f"   control fires (some m give g=0): {sorted(m for m in results if len(results[m][1]) == 0)}")
print(f"   => the 120 deg law at the anchor needs only m in {g2}, NOT m = 1 alone."
      if len(g2) > 1 else "   => g=2 pins m uniquely.")

print()
print("=" * 78)
print("T4  secp256k1: the scale-free inputs, exact ints")
print("=" * 78)
p = 2**256 - 2**32 - 977
B = 7
assert p == 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
print(f"   p = 2^256 - 2^32 - 977")
print(f"   p mod 4  = {p % 4}")
print(f"   p mod 3  = {p % 3}")
print(f"   p mod 12 = {p % 12}")
cub = pow(B, (p - 1) // 3, p)
print(f"   7^((p-1)/3) mod p == 1 ?  {cub == 1}   -> 7 is a cubic "
      f"{'residue' if cub == 1 else 'NON-residue'} mod p")
print(f"   => m-law branch (p=7 mod 12, B a cubic non-residue) predicts m = 1")
print(f"   => J(chi3,chi4) = -p  (p = 1 mod 3)")
print()
print("   Sanity: is the m=1 prediction consistent with |alpha| = sqrt(p) and char(t)=t^4+m p t^2+p^2?")
# t = sqrt(p) z  =>  p^2 (z^4 + m z^2 + 1). Exact check of the normalisation, symbolically:
# char(t) = t^4 + m p t^2 + p^2 ; substitute t^2 = p u  ->  p^2 u^2 + m p^2 u + p^2 = p^2(u^2+mu+1). OK
print("   char(t) = t^4 + m*p*t^2 + p^2, t = sqrt(p)*z  ->  p^2*(z^4 + m*z^2 + 1) : normalisation OK")
