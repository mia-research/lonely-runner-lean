"""What the prime-order theorem does for n = 5.

5 is prime, so `flankWorks_of_prime` applies: if 5 divides neither the flank nor any disparity,
EVERY flank hosts a lonely opening -- PROVED, axiom-clean.

Earlier the n=5 largest-flank statement (FourClears / DoorLargestFlank) was [EMPIRICAL] over
172M sets, with only the ratio-condition region `d_max <= 4 d_min` proved (clear_at_last_opening,
42.7%).  How much is proved now, and what is left?
"""
import math
from itertools import combinations

def works_at(c, e, n=5):
    M = n*e; lo, hi = e, (n-1)*e
    return any(all(lo <= (d*(n*j+1)) % M <= hi for d in c) for j in range(e))

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

for hi in (60, 120):
    tot = nonres = ratio = union = rem = rem_fail = 0
    ex = []
    for c in combinations(range(1, hi+1), 4):
        if not prim(c): continue
        tot += 1
        e = c[-1]
        A = all(d % 5 != 0 for d in c)          # non-resonant: PROVED by the prime theorem
        B = e <= 4 * c[0]                        # ratio condition: PROVED by clear_at_last_opening
        if A: nonres += 1
        if B: ratio += 1
        if A or B: union += 1
        else:
            rem += 1
            if not works_at(c, e):
                rem_fail += 1
                if len(ex) < 5: ex.append(c)
    print(f"n=5, card 4, primitive subsets of [1,{hi}]: {tot} sets")
    print(f"   PROVED, non-resonant (prime theorem) : {nonres:>9}  ({100*nonres/tot:5.2f}%)")
    print(f"   PROVED, ratio condition              : {ratio:>9}  ({100*ratio/tot:5.2f}%)")
    print(f"   PROVED, union of the two             : {union:>9}  ({100*union/tot:5.2f}%)")
    print(f"   REMAINING (resonant AND wide ratio)  : {rem:>9}  ({100*rem/tot:5.2f}%)")
    print(f"      of which the largest flank fails  : {rem_fail:>9}")
    if ex: print(f"      examples of failures: {ex}")
    print()
