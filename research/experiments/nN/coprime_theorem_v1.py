"""CANDIDATE: if gcd(d, n) = 1 for every disparity d, the LARGEST flank hosts a lonely opening.

Every largest-flank failure observed at k = 6 contained a disparity sharing a factor with n,
at every order 7..14 (resonance_v1.out).  Tested here across orders and blocker counts, and
against the contrapositive -- among resonant sets, failures should exist.
"""
import math
from itertools import combinations

def works(c, n):
    e = c[-1]; M = n*e; lo, hi = e, (n-1)*e
    return any(all(lo <= (d*(n*j+1)) % M <= hi for d in c) for j in range(e))

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

RANGE = {4: 26, 5: 22, 6: 16, 7: 14, 8: 12}
print("counterexamples to: all gcd(d,n)=1  =>  largest flank works")
print(f"{'n':>3} {'card':>5} {'coprime sets':>13} {'FAILURES':>9} {'resonant sets':>14} {'failures':>9}")
total_cx = 0
for n in range(5, 15):
    for card in (4, 5, 6, 7, 8):
        if card > n - 1: continue
        hi = RANGE[card]
        cop_t = cop_f = res_t = res_f = 0
        for c in combinations(range(1, hi+1), card):
            if not prim(c): continue
            coprime = all(math.gcd(d, n) == 1 for d in c)
            bad = not works(c, n)
            if coprime:
                cop_t += 1; cop_f += bad
            else:
                res_t += 1; res_f += bad
        if cop_f: total_cx += cop_f
        flag = "  *** COUNTEREXAMPLE ***" if cop_f else ""
        if res_f or cop_f:
            print(f"{n:>3} {card:>5} {cop_t:>13} {cop_f:>9} {res_t:>14} {res_f:>9}{flag}")
print()
print(f"TOTAL COUNTEREXAMPLES across all (n, card) tested: {total_cx}")
