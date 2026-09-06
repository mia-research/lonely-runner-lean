#!/usr/bin/env python3
"""The phi(n) permutation law is what produces the n=8 block structure.

The phi(n) AP law (lrc_ap_phi_n_law_v1.md, Thm 3.1) and the n=11 paper's Step 3
"equally-spaced preimages" lemma both turn on one fact:

    j |-> j*r (mod n)  is a permutation of Z/n  iff  gcd(r,n) = 1.

n = 11 is PRIME, so every speed not divisible by 11 permutes.  n = 8 is not:
only phi(8) = 4 of the 8 residues are units, so half the speeds degenerate.

CLAIM TESTED HERE.  Over the FULL target range {1,...,N-1}, N = n*p, partition
the targets into the p residue classes mod p; each class has n members
j = r + p*t, t in Z/n.  Since j*v mod N = (r*v mod N) + p*((t*v) mod n), the
block index moves by t*v mod n.  So t |-> t*v is g-to-1 onto the subgroup
(g)Z/n, where g = gcd(v,n), and the covering window is 2 of the n blocks.
Hence the number of members of a class that v covers is

    g * |image  intersect  (window - a)|,

i.e. coverage arrives in LUMPS OF SIZE g = gcd(v,n).  Predicted per-class counts:

    g = 1  ->  exactly 2      (unit: finest possible granularity)
    g = 2  ->  exactly 2      (window has one even and one odd block)
    g = 4  ->  0 or 4
    g = 8  ->  0 or 8

Tested for n = 8 at several primes, and for n = 11 (prime) as the control where
the law predicts no degeneracy at all.
"""
from collections import Counter
from math import gcd

def profile(n, p):
    N = n * p
    out = {}
    for v in range(1, N):
        if v % p == 0:
            continue
        g = gcd(v, n)
        c = Counter()
        for r in range(1, p + 1):
            cnt = sum(1 for t in range(n)
                      if (lambda x: x < p or x > N - p)(((r + p * t) * v) % N))
            c[cnt] += 1
        out.setdefault(g, Counter()).update(c)
    return out

pred = {1: {2}, 2: {2}, 4: {0, 4}, 8: {0, 8}}
for n, ps in [(8, [31, 47, 163]), (11, [13, 23])]:
    print(f"\nn = {n}   (phi({n}) = {sum(1 for a in range(n) if gcd(a,n)==1)}, "
          f"{'PRIME' if all(n%d for d in range(2,n)) else 'composite'})")
    for p in ps:
        prof = profile(n, p)
        print(f"  p = {p}")
        for g in sorted(prof):
            seen = set(prof[g])
            tag = ""
            if n == 8:
                tag = "  MATCHES prediction" if seen == pred.get(g, set()) else "  <-- MISMATCH"
            print(f"    gcd(v,{n}) = {g}:  per-class counts seen = {sorted(seen)}"
                  f"   lump size = {g}{tag}")
