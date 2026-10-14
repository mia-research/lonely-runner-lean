"""Theorem 14.1 (rescaled_residue): a multiple c*s_i sits at s_i*(c mod 8) at EVERY candidate of
s_i, independent of the opening q.  So multiples of s_i are CONSTANT on the family: all or nothing.

Dichotomy per family s_i:
  - if some multiple of s_i in the profile has 8 | quotient  ->  family entirely dead
  - otherwise those readings NEVER block it, and only NON-multiples can vary

Measure what that buys: families killed outright, and the varying-blocker count on survivors.
"""
from itertools import combinations
from collections import Counter

def blocks(sj, A, si):
    M = 8*si; r = (sj*A) % M
    return min(r, M-r) < si
def cands(si):
    A = si + ((1-si) % 8); out=[]
    while A <= 7*si: out.append(A); A += 8
    return out

tot=0; killed=Counter(); vary=Counter(); allkilled=0
const_confirm = 0; const_checked = 0
for combo in combinations(range(2, 26), 6):
    if not any(x % 8 == 0 for x in combo): continue
    S = (1,) + combo; tot += 1
    dead = 0
    for si in S:
        mult = [sj for sj in S if sj % si == 0 and sj != si]
        # confirm constancy: a multiple blocks all candidates or none
        for sj in mult:
            vals = {blocks(sj, A, si) for A in cands(si)}
            const_checked += 1
            if len(vals) == 1: const_confirm += 1
        if any((sj // si) % 8 == 0 for sj in mult):
            dead += 1
        else:
            nonmult = [sj for sj in S if sj % si != 0]
            vary[len(nonmult)] += 1
    killed[dead] += 1
    if dead == len(S): allkilled += 1
print(f"Branch B profiles, readings [2,25] : {tot:,}\n")
print(f"  constancy of multiples across a family: {const_confirm:,}/{const_checked:,} confirmed"
      f"  ({'ALL' if const_confirm==const_checked else 'NOT ALL'})")
print(f"\n  families killed outright per profile: {dict(sorted(killed.items()))}")
print(f"  profiles with EVERY family killed    : {allkilled:,}")
print(f"\n  varying-blocker count on surviving families: {dict(sorted(vary.items()))}")
