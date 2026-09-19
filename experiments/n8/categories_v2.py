"""v1's C3 was an artefact of range bias: it never sampled profiles with all readings small.
Redo with EXHAUSTIVE small arms, where the known counterexamples live."""
from itertools import combinations
from math import gcd
import random

def clear_at(S, sk):
    M = 8*sk; A = sk + ((1-sk) % 8)
    while A <= 7*sk:
        if all(min((si*A) % M, M - (si*A) % M) >= sk for si in S): return A
        A += 8
    return None

print("control: the known counterexample to the s_max rule")
S0 = (1,2,3,4,5,7,8)
print(f"  {S0}  s_k = s_max = 8  ->  {clear_at(S0, 8)}   (None expected)\n")

# C1 divisor-closed, EXHAUSTIVE over all m with >= 7 divisors, all 7-subsets containing 1 and m
tot = fail = 0; ex = []
for m in range(24, 1200):
    ds = [d for d in range(1, m+1) if m % d == 0]
    if len(ds) < 7: continue
    mid = [d for d in ds if d != 1 and d != m]
    for c in combinations(mid, 5):
        S = (1,) + c + (m,)
        tot += 1
        if clear_at(S, m) is None:
            fail += 1
            if len(ex) < 4: ex.append(S)
print(f"C1  divisor-closed, EXHAUSTIVE m<1200   rule s_k = s_max   {tot:>9,} profiles   fails {fail:>7,}")
for S in ex: print(f"      e.g. {S}")

# C3 collider is largest, EXHAUSTIVE small
tot = fail = 0; ex = []
for m in range(8, 200, 8):
    for c in combinations(range(2, m), 5):
        S = (1,) + c + (m,)
        tot += 1
        if clear_at(S, m) is None:
            fail += 1
            if len(ex) < 4: ex.append(S)
        if tot > 4000000: break
    if tot > 4000000: break
print(f"\nC3  collider largest, EXHAUSTIVE         rule s_k = s_max   {tot:>9,} profiles   fails {fail:>7,}")
for S in ex: print(f"      e.g. {S}")

# C4 all readings share a factor with s_max, EXHAUSTIVE small
tot = fail = 0; ex = []
for m in range(4, 300):
    pool = [x for x in range(2, m) if gcd(x, m) > 1]
    if len(pool) < 5: continue
    for c in combinations(pool, 5):
        S = (1,) + c + (m,)
        tot += 1
        if clear_at(S, m) is None:
            fail += 1
            if len(ex) < 4: ex.append(S)
        if tot > 3000000: break
    if tot > 3000000: break
print(f"\nC4  shares a factor with s_max, EXHAUST  rule s_k = s_max   {tot:>9,} profiles   fails {fail:>7,}")
for S in ex: print(f"      e.g. {S}")
