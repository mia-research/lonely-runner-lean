"""Collapsed difference sets: card < n-1, which arise when two runners are equidistant in speed.

|v i - v k| collapses when v i and v j sit symmetrically about v k, so a subject at order n can
present fewer than n-1 distinct disparities.  The main sweeps only covered full-card sets.
This checks the flank-rank property on the collapsed cards at n = 5 and n = 6.
"""
import math
from itertools import combinations

def works_at(c, e, n):
    M = n*e; lo, hi = e, (n-1)*e
    for j in range(e):
        a = n*j + 1
        if all(lo <= (d*a) % M <= hi for d in c): return True
    return False

def best_rank(c, n):
    for r, e in enumerate(sorted(set(c), reverse=True), 1):
        if works_at(c, e, n): return r
    return 99

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g, x)
    return g == 1

for n, target_rank, cards, HI in [(5, 1, [1,2,3], 300), (6, 2, [1,2,3,4], 160)]:
    print(f"=== n={n}: claim is best rank <= {target_rank} (full card is {n-1}) ===")
    for card in cards:
        tot = bad = 0; worst = 0; ex = []
        hi = HI if card <= 2 else (HI//2 if card == 3 else HI//4)
        for c in combinations(range(1, hi+1), card):
            if not prim(c): continue
            tot += 1
            r = best_rank(c, n)
            worst = max(worst, r)
            if r > target_rank:
                bad += 1
                if len(ex) < 5: ex.append(c)
        flag = "OK" if bad == 0 else f"*** {bad} EXCEED rank {target_rank} ***"
        print(f"   card {card}, [1,{hi}]: {tot:>8} sets   worst rank {worst}   {flag}   {ex if ex else ''}")
    print()
