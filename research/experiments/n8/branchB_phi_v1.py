"""MANUSCRIPT_v19 section 15 / Appendix A, Branch B: profiles 1 = s1 < ... < s7 (integers) with at
least one reading divisible by 8.  The manuscript records two regularities as "measured and
unexplained":

   (i)  at least TWO readings always supply a witness, never one and never zero;
   (ii) the supplying reading is never the smallest.

Test whether either is a phi(8) fact.  Population reproduced exactly: {1} + 6-subset of [2,30]
with at least one of {8,16,24}.  (C(29,6) - C(26,6) = 244,790, matching the manuscript.)
"""
from itertools import combinations
import math, collections
n = 8
def supplies(S, s):
    """does reading s supply a witness?  A = 1 mod 8, s <= A <= 7s, all s'A mod 8s in [s,7s]"""
    M = n*s
    for A in range(s, 7*s+1):
        if A % n != 1 % n: continue
        if all(s <= (t*A) % M <= (n-1)*s for t in S): return A
    return None
pop = 0; cnt = collections.Counter(); never_small = 0
unit_match = 0; odd_match = 0; ex = []
for rest in combinations(range(2,31), 6):
    if not any(x % 8 == 0 for x in rest): continue
    S = (1,) + rest
    pop += 1
    sup = [s for s in S if supplies(S, s)]
    cnt[len(sup)] += 1
    if 1 not in sup: never_small += 1
    # phi hypotheses, fixed in advance
    if set(sup) == set(s for s in S if math.gcd(s,8)==1): unit_match += 1
    if set(sup) == set(s for s in S if s % 2 == 1): odd_match += 1
    if len(sup) <= 1 and len(ex) < 4: ex.append((S, sup))
print(f"Branch-B profiles reproduced: {pop}   (manuscript: 244,790)")
print(f"  number of supplying readings: {dict(sorted(cnt.items()))}")
print(f"  smallest reading (=1) never supplies: {never_small}/{pop}")
print(f"  supplying set == readings coprime to 8: {unit_match}/{pop}")
print(f"  supplying set == odd readings         : {odd_match}/{pop}")
if ex: print(f"  profiles with <=1 supplier: {ex}")
