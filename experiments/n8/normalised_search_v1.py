#!/usr/bin/env python3
"""Rosenfeld's Lemma 7 search with the unit-scaling normalisation.

SYMMETRY.  Let N = n*p, n = k+1.  For a unit c mod N, the map v -> cv, j -> c^{-1}j
permutes Z/N, preserves ||jv/N||, preserves 2-adic and p-adic valuations, and hence
preserves both "T covers every target" and the gcd side condition.  Folding by the
v <-> N-v symmetry, the group acting is (Z/N)^* / {+-1}, of order phi(N)/2.

The gcd condition requires, for every prime q | N, at least two speeds of T with
q not dividing them.  For n = 7 and n = 8 (single prime power in n) that forces T
to contain a speed coprime to N.  Scaling by its inverse:

    WLOG  1 in T.

That divides the search space by phi(N)/2  ( = 324 for N = 1304 ).

FORCED COARSE SPEED (n = 8, independent of the normalisation).  The target j = p
has j*v mod N = p*(v mod n), which lies in [0,p) only for v = 0 mod n.  So every
cover contains at least one speed with n | v.  Same for j = 3p.
"""
import sys
from math import gcd
from itertools import combinations
from functools import reduce

def bad_cover_normalised(k, p, verbose=False):
    n = k + 1
    N = n * p
    H = N // 2
    J = list(range(1, H + 1))
    idx = {j: i for i, j in enumerate(J)}
    V = [v for v in range(1, H + 1) if v % p != 0]
    cov = {}
    for v in V:
        m = 0
        for j in J:
            r = (j * v) % N
            if r < p or r > N - p:
                m |= 1 << idx[j]
        cov[v] = m
    FULL = (1 << len(J)) - 1
    maxcov = max(bin(m).count("1") for m in cov.values())
    primes_of_n = {q for q in range(2, n + 1) if n % q == 0 and all(q % d for d in range(2, q))}

    def gcd_ok(T):
        return all(sum(1 for v in T if v % q) >= 2 for q in primes_of_n)

    # speeds covering each target, precomputed
    hit = {j: [v for v in V if (cov[v] >> idx[j]) & 1] for j in J}

    found = []

    def rec(chosen, mask):
        if mask == FULL:
            if gcd_ok(chosen):
                found.append(list(chosen))
                return True
            return False
        if len(chosen) == k:
            return False
        rem = FULL & ~mask
        nrem = bin(rem).count("1")
        if nrem > (k - len(chosen)) * maxcov:
            return False
        lb = (rem & -rem).bit_length() - 1
        for v in hit[J[lb]]:
            if v in chosen:
                continue
            if rec(chosen + [v], mask | cov[v]):
                return True
        return False

    ok = rec([1], cov[1])
    if verbose and ok:
        print("   witness:", found[0])
    return ok

if __name__ == "__main__":
    print("VALIDATION against lemma7_criterion_v1 / the paper's k=6 pattern")
    print("(paper: k=6 Lemma 7 holds at 13 and 19, fails at 17, 23, 29, holds from 31 up)")
    for p in [13, 17, 19, 23, 29, 31, 37, 41]:
        b = bad_cover_normalised(6, p)
        print(f"   k=6 p={p:>3}  bad cover exists: {str(b):>5}   Lemma 7 {'FAILS' if b else 'applies'}")
        sys.stdout.flush()
    print()
    for p in [7, 11, 13]:
        b = bad_cover_normalised(3, p)
        print(f"   k=3 p={p:>3}  bad cover exists: {str(b):>5}")
        sys.stdout.flush()
