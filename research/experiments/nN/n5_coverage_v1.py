"""n=5: total PROVED coverage now, from three theorems that are all axiom-clean in Lean.

  (P1) non-resonant            -> LRC.Resonance.flankWorks_of_prime      (5 is prime)
  (P2) d_max <= 4*d_min        -> LRC.FlankFinite.clear_at_last_opening
  (P3) d_max <= 15             -> LRC.FlankFinite.four_clears_small      (decide, no axioms)

Everything outside the union is the residue.  Reported with the number of working openings, so
the remaining margin is visible.
"""
import math
from itertools import combinations

def count_openings(c, n=5, cap=3):
    e = c[-1]; M = n*e; lo, hi = e, (n-1)*e
    cnt = 0
    for j in range(e):
        a = n*j + 1
        if all(lo <= (d*a) % M <= hi for d in c):
            cnt += 1
            if cnt >= cap: return cap
    return cnt

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

for hi in (60, 120):
    tot = cov = rem = 0
    minopen = 99; worst = None; zero = 0
    for c in combinations(range(1, hi+1), 4):
        if not prim(c): continue
        tot += 1
        e = c[-1]
        P1 = all(d % 5 != 0 for d in c)
        P2 = e <= 4 * c[0]
        P3 = e <= 15
        if P1 or P2 or P3: cov += 1
        else:
            rem += 1
            w = count_openings(c)
            if w == 0: zero += 1
            if w < minopen: minopen, worst = w, c
    print(f"n=5, card 4, primitive subsets of [1,{hi}]: {tot} sets")
    print(f"   PROVED by P1 or P2 or P3 : {cov:>9}  ({100*cov/tot:5.2f}%)")
    print(f"   residue                  : {rem:>9}  ({100*rem/tot:5.2f}%)")
    print(f"   residue: min # of working openings = {minopen} (capped at 3), at {worst}")
    print(f"   residue: sets with ZERO openings   = {zero}")
    print()
