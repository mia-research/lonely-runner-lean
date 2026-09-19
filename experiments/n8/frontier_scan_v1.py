"""Systematic scan: which (sub-category, proved-mechanism) pairs give 100% coverage?

Sub-categories of integer Branch B (some 8 | s_j).  Mechanisms are OUR OWN:
  spine      x = u odd in {1,3,5,7}                 (Branch A's mechanism, Guard.odd_clear_of_not_dvd)
  unit-orbit all four odd u, i.e. the Klein orbit
  endpoint   x = (8k+1)/s for a reading s           (reach_mem / witness_normalised)
  rescale    take s_k = s and use rescaled_blocks_iff / divisor_reduces
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd

def clear_x(S, x):
    """x in [1,7] rational; clear iff ||s x / 8|| >= 1/8 for all s in S."""
    for s in S:
        y = F(s) * x
        k = round(y / 8)
        if abs(y - 8*k) < 1: return False
    return True

def spine(S):
    return any(clear_x(S, F(u)) for u in (1,3,5,7))
def endpoint(S):
    for s in S:
        k = 0
        while F(8*k+1, s) <= 7:
            if F(8*k+1, s) >= 1 and clear_x(S, F(8*k+1, s)): return True
            k += 1
    return False

CATS = {
 "all Branch B":                 lambda S: any(s % 8 == 0 for s in S),
 "exactly one collider":         lambda S: sum(1 for s in S if s % 8 == 0) == 1,
 "collider is a power of 2":     lambda S: any(s % 8 == 0 and (s & (s-1)) == 0 for s in S),
 "all non-colliders odd":        lambda S: any(s%8==0 for s in S) and all(s%2 or s%8==0 for s in S),
 "all readings divide s_max":    lambda S: all(max(S) % s == 0 for s in S) and any(s%8==0 for s in S),
 "collider = s_max":             lambda S: max(S) % 8 == 0,
 "collider = s_max, others odd": lambda S: max(S)%8==0 and all(s%2 for s in S if s!=max(S)),
 "pairwise coprime non-units":   lambda S: any(s%8==0 for s in S) and all(
                                     gcd(a,b)==1 for a,b in combinations([s for s in S if s>1],2)),
}
RULES = {"spine": spine, "endpoint": endpoint,
         "spine or endpoint": lambda S: spine(S) or endpoint(S)}

tot = {k:0 for k in CATS}
hit = {(k,r):0 for k in CATS for r in RULES}
for combo in combinations(range(2, 26), 6):
    S = (1,) + combo
    for ck, cf in CATS.items():
        if not cf(S): continue
        tot[ck] += 1
        for rk, rf in RULES.items():
            if rf(S): hit[(ck,rk)] += 1
print(f"{'sub-category':<32} {'profiles':>8} {'spine':>8} {'endpt':>8} {'either':>8}")
for ck in CATS:
    n = tot[ck]
    if n == 0: print(f"{ck:<32} {0:>8}"); continue
    row = "  ".join(f"{100*hit[(ck,rk)]/n:6.2f}%" for rk in RULES)
    star = "   <-- 100%" if hit[(ck,"spine or endpoint")] == n else ""
    print(f"{ck:<32} {n:>8,} {row}{star}")
