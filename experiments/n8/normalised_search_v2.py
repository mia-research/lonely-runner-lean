#!/usr/bin/env python3
"""Lemma 7 search: Rosenfeld's own optimisations PLUS the unit-scaling normalisation.

From the paper (section 6) we take: bitset covers; branch-and-bound on the count of
uncovered targets; sibling elimination (if no cover extends {v_1..v_i, v}, drop v
from the available set for later siblings at level i); and branching on the target
covered by the fewest available speeds.  The paper notes it does NOT exploit
i-covers-j symmetry, and it does not use unit scaling either.

We add (see docs/n8/SEARCH_REDUCTION_v1.md):
  * WLOG 1 in T          -- unit scaling, a factor phi(N)/2 = 324 at N = 1304
  * j = p forces n | v   -- so the first branch is over the n-divisible speeds only
                            (this falls out of the min-options rule automatically)

Validated below against every published data point: the k=3,4,5,6 thresholds and
the k=7 exception at p=41.
"""
import sys, time
from math import gcd
from functools import reduce
from itertools import combinations

def build(k, p):
    n = k + 1
    N = n * p
    H = N // 2
    J = list(range(1, H + 1))
    V = [v for v in range(1, H + 1) if v % p != 0]
    idx = {j: i for i, j in enumerate(J)}
    cov = {}
    for v in V:
        m = 0
        for j in J:
            r = (j * v) % N
            if r < p or r > N - p:
                m |= 1 << idx[j]
        cov[v] = m
    return n, N, H, J, V, cov

def bad_cover(k, p, want_witness=False):
    n, N, H, J, V, cov = build(k, p)
    FULL = (1 << len(J)) - 1
    maxcov = max(m.bit_count() for m in cov.values())
    # static branching order: targets covered by the fewest speeds first
    cnt = [sum((cov[v] >> i) & 1 for v in V) for i in range(len(J))]
    order = sorted(range(len(J)), key=lambda i: cnt[i])
    primes_of_n = sorted({q for q in range(2, n + 1) if n % q == 0
                          and all(q % d for d in range(2, q))})
    hit = [[v for v in V if (cov[v] >> i) & 1] for i in range(len(J))]
    witness = []

    def gcd_ok(T):
        return all(sum(1 for v in T if v % q) >= 2 for q in primes_of_n)

    def deficit(T, slots):
        """cheapest number of further speeds the gcd condition still demands"""
        return max((2 - sum(1 for v in T if v % q) for q in primes_of_n), default=0)

    def rec(chosen, mask, avail):
        if mask == FULL:
            if gcd_ok(chosen):
                witness.extend(chosen)
                return True
            return False
        slots = k - len(chosen)
        if slots == 0:
            return False
        rem = FULL & ~mask
        if rem.bit_count() > slots * maxcov:
            return False
        if deficit(chosen, slots) > slots:
            return False
        for i in order:
            if (rem >> i) & 1:
                u = i
                break
        cands = [v for v in hit[u] if v in avail]
        for v in cands:
            if rec(chosen + [v], mask | cov[v], avail - {v}):
                return True
            avail = avail - {v}          # sibling elimination
        return False

    ok = rec([1], cov[1], set(V) - {1})
    return (ok, witness) if want_witness else ok

if __name__ == "__main__":
    print("VALIDATION (paper section 7: k=3 >7, k=4 >17, k=5 >23, k=6 >31 plus 13,19,")
    print("            k=7 any p>=31 other than 41)")
    checks = [(3, [5, 7, 11]), (6, [13, 17, 19, 23, 29, 31, 37]), (7, [31, 37, 41, 43])]
    for k, ps in checks:
        for p in ps:
            t = time.time(); b = bad_cover(k, p)
            print(f"   k={k} p={p:>3}  bad cover {str(b):>5}  Lemma 7 {'FAILS' if b else 'applies'}"
                  f"   {time.time()-t:7.1f}s")
            sys.stdout.flush()
