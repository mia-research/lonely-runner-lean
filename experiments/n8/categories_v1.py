"""Which categories does a FIXED choice of s_k close?  A rule, not a search.

gcd_covariant: blocks(s_i, A, s_k) <-> blocks(a, A, b),  g=gcd(s_i,s_k), a=s_i/g, b=s_k/g.
rescaled_blocks_iff: b = 1  =>  blocks iff 8 | a.
So a category is closable when the b's are controlled by construction.
"""
from itertools import combinations
import random

def clear_at(S, sk):
    """Is some s_k-candidate clear?  Return the witness A, or None."""
    M = 8*sk; A = sk + ((1-sk) % 8)
    while A <= 7*sk:
        if all(min((si*A) % M, M - (si*A) % M) >= sk for si in S): return A
        A += 8
    return None

def divisors_upto(m, k):
    return [d for d in range(1, m+1) if m % d == 0][:k]

print("Each row: a CATEGORY + a FIXED rule for s_k.  'fails' = the rule gave no witness.\n")
rng = random.Random(20260919)

# C1 divisor-closed: every reading divides the largest.  Rule: s_k = s_max.
tot = fail = 0; ex=[]
for m in range(8, 3000):
    ds = [d for d in range(1, m+1) if m % d == 0]
    if len(ds) < 7: continue
    for _ in range(40):
        S = tuple(sorted(set(rng.sample(ds[:-1], 6)) | {m, 1}))
        if len(S) != 7: continue
        tot += 1
        if clear_at(S, max(S)) is None:
            fail += 1
            if len(ex)<3: ex.append(S)
print(f"C1  divisor-closed (all s_i | s_max)       rule s_k = s_max      "
      f"{tot:>7,} profiles   fails {fail:>6,}")
for S in ex: print(f"      e.g. {S}")

# C2 same, but rule s_k = 1  (i.e. Branch A's move) -- for contrast
tot = fail = 0
for m in range(8, 1500):
    ds = [d for d in range(1, m+1) if m % d == 0]
    if len(ds) < 7: continue
    for _ in range(40):
        S = tuple(sorted(set(rng.sample(ds[:-1], 6)) | {m, 1}))
        if len(S) != 7: continue
        tot += 1
        if clear_at(S, 1) is None: fail += 1
print(f"C2  same profiles                          rule s_k = 1          "
      f"{tot:>7,} profiles   fails {fail:>6,}")

# C3 Branch B with the collider largest and dividing nothing special. Rule s_k = s_max.
tot = fail = 0; ex=[]
for _ in range(200000):
    S = tuple(sorted(set([1] + rng.sample(range(2, 500), 5) + [8*rng.randrange(1, 60)])))
    if len(S) != 7 or max(S) % 8: continue
    tot += 1
    if clear_at(S, max(S)) is None:
        fail += 1
        if len(ex)<3: ex.append(S)
print(f"C3  collider is the largest reading        rule s_k = s_max      "
      f"{tot:>7,} profiles   fails {fail:>6,}")
for S in ex: print(f"      e.g. {S}")

# C4 every non-unit reading shares a factor >1 with s_max.  Rule s_k = s_max.
tot = fail = 0; ex=[]
from math import gcd
for _ in range(300000):
    S = tuple(sorted(set([1] + rng.sample(range(2, 400), 6))))
    if len(S) != 7: continue
    m = max(S)
    if any(gcd(x, m) == 1 for x in S if x != 1): continue
    tot += 1
    if clear_at(S, m) is None:
        fail += 1
        if len(ex)<3: ex.append(S)
print(f"C4  all readings share a factor with s_max rule s_k = s_max      "
      f"{tot:>7,} profiles   fails {fail:>6,}")
for S in ex: print(f"      e.g. {S}")
