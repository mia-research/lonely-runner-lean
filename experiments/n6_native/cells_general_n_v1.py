#!/usr/bin/env python3
"""(c) The cell reduction at general n.
(1) Verify: at flank e = n*E, d = n*q + s (1 <= s <= n-1), opening j = u*E + i,
    e <= d(nj+1) mod ne <= (n-1)e   iff   (a + s*u) mod n in {1..n-2},  a = ((d*i+q) mod nE) // E.
(2) Coarse blocking: residue r blocks shift u when (r*u) mod n in {0, n-1}. List the residue SETS
    R within {1..n-1}, |R| <= n-2 (the non-flank differences at order n), that block every shift
    u in {0..n-1}; report the minimum size and the minimal sets, and phi(n)."""
import sys, math
from itertools import combinations
for n in (6, 7, 8):
    checked = mism = 0
    for E in range(1, 7):
        e = n * E
        for d in range(1, 3 * e):
            if d % n == 0: continue
            q, s = divmod(d, n)
            for u in range(n):
                for i in range(E):
                    j = u * E + i
                    direct = e <= (d * (n * j + 1)) % (n * e) <= (n - 1) * e
                    a = ((d * i + q) % (n * E)) // E
                    cell = 1 <= (a + s * u) % n <= n - 2
                    checked += 1; mism += direct != cell
    blocks = lambda r, u: (r * u) % n in (0, n - 1)
    minimal = []
    for size in range(1, n - 1):
        for R in combinations(range(1, n), size):
            if all(any(blocks(r, u) for r in R) for u in range(n)):
                if not any(set(M) <= set(R) for M in minimal): minimal.append(R)
    phi = sum(1 for k in range(1, n) if math.gcd(k, n) == 1)
    sizes = sorted({len(M) for M in minimal})
    print(f"n={n}: cell criterion checked {checked} openings, mismatches {mism}; phi(n)={phi}; blockers available n-2={n-2}")
    print(f"   minimal residue sets blocking every coarse shift: {minimal if minimal else 'NONE (some shift always free)'}; sizes {sizes}")
