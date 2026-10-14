"""RULE 2 under test: in the residue, are the low-opening sets bounded in d_max?

If sets with <= T openings all have d_max <= B(T) with B stable as the range grows, the residue
splits into a finite check (d_max <= B) plus a margin argument (>= T+1 openings above it).
That is the same shape that worked for the tight families at orders 5 and 6.
"""
import math, sys
from itertools import combinations

def n_open(c, cap=6):
    e = c[-1]; M = 5*e; cnt = 0
    for j in range(e):
        a = 5*j+1
        ok = True
        for d in c:
            if not (e <= (d*a) % M <= 4*e): ok = False; break
        if ok:
            cnt += 1
            if cnt >= cap: return cap
    return cnt

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

def in_residue(c):
    e = c[-1]
    return any(d % 5 == 0 for d in c[:-1]) and e > 4*c[0] and e > 15

print(f"{'range':>9} {'residue sets':>13} " + " ".join(f"max d_max @<={T}" for T in (2,3,4,5)))
for hi in (40, 50, 60, 70, 80):
    sets = [c for c in combinations(range(1, hi+1), 4) if prim(c) and in_residue(c)]
    row = []
    for T in (2,3,4,5):
        sub = [c for c in sets if n_open(c) <= T]
        row.append(f"{max((max(c) for c in sub), default=0):>14}")
    print(f"{('[1,'+str(hi)+']'):>9} {len(sets):>13} " + "".join(row))
print()
print("=== the <=2 family in full at [1,80] ===")
sets = [c for c in combinations(range(1, 81), 4) if prim(c) and in_residue(c)]
low = sorted(c for c in sets if n_open(c) <= 2)
print(f"   {len(low)} sets, max element {max(max(c) for c in low)}")
for c in low: print(f"      {c}   e mod 5 = {c[-1]%5}")
