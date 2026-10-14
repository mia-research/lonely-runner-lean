#!/usr/bin/env python3
"""Is f(8,p) >= 6 for every odd prime p?  Decide it, before trying to prove it.

f(8,p) = min number of dilates w^{-1}A needed to cover Z/p, where A = {|s| <= h},
h = floor((p-1)/8).  "f >= 6" is exactly "no 5 dilates cover", i.e.

    for every w_1..w_5 in (Z/p)*, there is r != 0 with |r w_i|_p > h for all i.

Decided exactly by depth-5 branch-and-bound: the lowest uncovered residue must be
covered by SOME dilate, so branching over the dilates containing it is complete.
Scale invariance (union size is invariant under w_i -> c w_i) lets the first dilate
be w = 1.  M[-w] = M[w] since A = -A, so w ranges over 1..(p-1)/2.
"""
import sys

def can_cover_with(p, x):
    h = (p - 1) // 8
    if h == 0: return False                      # A = {0}
    A = {s % p for s in range(-h, h + 1)}
    W = list(range(1, (p - 1) // 2 + 1))
    M = {w: sum(1 << r for r in range(p) if (r * w) % p in A) for w in W}
    FULL = (1 << p) - 1
    arc = 2 * h + 1
    by_r = [[w for w in W if (M[w] >> r) & 1] for r in range(p)]
    def rec(u, d):
        rem = FULL & ~u
        if rem == 0: return True
        if d == x: return False
        if rem.bit_count() > (x - d) * arc: return False
        lb = (rem & -rem).bit_length() - 1
        for w in by_r[lb]:
            if rec(u | M[w], d + 1): return True
        return False
    return rec(M[1], 1)                          # WLOG 1 is in the set

def primes(lo, hi):
    s = [True] * (hi + 1); s[0] = s[1] = False
    for i in range(2, int(hi ** .5) + 1):
        if s[i]:
            for j in range(i * i, hi + 1, i): s[j] = False
    return [i for i in range(lo, hi + 1) if s[i]]

if __name__ == "__main__":
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    fails = []
    for p in primes(lo, hi):
        h = (p - 1) // 8
        c5 = can_cover_with(p, 5)
        if c5:
            fails.append(p)
            print(f"p={p:>5} h={h:>4} |A|={2*h+1:>4}   5 DILATES COVER -> f(8,p) <= 5  ** CLAIM FALSE **", flush=True)
    print(f"\nprimes tested: {len(primes(lo,hi))} in [{lo},{hi}]")
    print(f"primes where 5 dilates cover (f <= 5): {len(fails)}  {fails}")
    print(f"f(8,p) >= 6 holds for: {len(primes(lo,hi)) - len(fails)} of {len(primes(lo,hi))}")
