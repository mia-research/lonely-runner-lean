#!/usr/bin/env python3
"""Check of the citation-verifier's refutation (2026-10-16): D = (1,2,3,4,L), L = lcm(1..Q0), kills every grid q <= Q0
(q | L puts the fastest runner on the subject at every c/q). Least lonely unit instant c/q, exact integers."""
import math
def blocks(d, c, q): x = (d * c) % q; return 6 * x < q or 6 * x > 5 * q
def qstar(S):
    q = 2
    while True:
        for c in range(1, q):
            if math.gcd(c, q) == 1 and not any(blocks(d, c, q) for d in S): return q, c
        q += 1
for Q0 in (6, 12, 20, 28, 40, 60):
    L = math.lcm(*range(1, Q0 + 1)); print(Q0, L, qstar((1, 2, 3, 4, L)))
