"""Category: divisor-closed, every middle quotient b_i = m/s_i <= 7.
Then small_b_blocks_iff makes every constraint bare non-divisibility, and any q coprime to 210
clears all of them.  Range for q: [(m-1)/8, (7m-1)/8], length 3m/4.
Jacobsthal g(210) = 10, so a coprime q exists once 3m/4 >= 10.

CLAIM: q = the least integer >= ceil((m-1)/8) coprime to 210 is always a witness.
"""
from itertools import combinations
from math import gcd

def blocks(si, A, sk):
    M = 8*sk; r = (si*A) % M
    return min(r, M-r) < sk

tot = fail = badrange = 0; exs = []
maxgap = 0
for m in range(8, 6000):
    # readings m/b for b in a 5-subset of {2..7} with b | m, plus 1 and m
    opts = [b for b in range(2, 8) if m % b == 0]
    if len(opts) < 5: continue
    for sub in combinations(opts, 5):
        S = tuple(sorted({1, m} | {m//b for b in sub}))
        if len(S) != 7: continue
        tot += 1
        lo = -(-(m-1)//8)                     # ceil((m-1)/8)
        hi = (7*m - 1)//8
        q = lo
        while q <= hi and gcd(q, 210) != 1: q += 1
        if q > hi:
            badrange += 1; continue
        maxgap = max(maxgap, q - lo)
        A = 8*q + 1
        if not (m <= A <= 7*m) or any(blocks(si, A, m) for si in S):
            fail += 1
            if len(exs) < 4: exs.append((S, m, q, A))
print(f"category: divisor-closed with every middle quotient <= 7")
print(f"  profiles (m < 6000, exhaustive over 5-subsets) : {tot:,}")
print(f"  rule 'least q >= ceil((m-1)/8) coprime to 210' FAILED : {fail:,}")
print(f"  range too short to contain such a q                  : {badrange:,}")
print(f"  largest search offset actually needed                : {maxgap}   (Jacobsthal g(210) = 10)")
for e in exs: print("     ", e)
