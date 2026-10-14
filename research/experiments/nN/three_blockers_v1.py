"""CANDIDATE: for every n >= 5, a difference set of card <= 4 has a lonely opening at its
LARGEST disparity.  (card 4 = 3 blockers, since the flank itself is never blocked.)

If true, n=5 DoorLargestFlank is the SPECIAL CASE where card <= 4 is automatic, and the real
theorem is about blocker count, not about the order.
"""
import math, random
from itertools import combinations

def works(c, n):
    e = c[-1]; M = n*e; lo, hi = e, (n-1)*e
    return any(all(lo <= (d*(n*j+1)) % M <= hi for d in c) for j in range(e))

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

print("=== card <= 4, exhaustive, across orders ===")
print(f"{'n':>4} {'range':>9} {'sets':>9} {'failures':>9}")
for n in [5,6,7,8,9,10,12,16,20,30,50]:
    tot = bad = 0; ex = []
    for m in (2,3,4):
        hi = {2: 90, 3: 50, 4: 34}[m]
        for c in combinations(range(1,hi+1), m):
            if not prim(c): continue
            tot += 1
            if not works(c, n):
                bad += 1
                if len(ex) < 3: ex.append(c)
    print(f"{n:>4} {'mixed':>9} {tot:>9} {bad:>9}   {ex if ex else ''}")

print()
print("=== card 4, wider ranges, at the orders that matter ===")
random.seed(17)
for n in [5,6,7,8]:
    tot = bad = 0; ex = []
    for _ in range(400000):
        c = tuple(sorted(random.sample(range(1, 4001), 4)))
        if not prim(c): continue
        tot += 1
        if not works(c, n):
            bad += 1
            if len(ex) < 3: ex.append(c)
    print(f"  n={n}  random card-4 from [1,4000]: {tot:>7} sets, {bad} failures  {ex if ex else ''}")

print()
print("=== and the contrast: card 5 (four blockers) ===")
for n in [6,7,8,9,10,11,12]:
    tot = bad = 0; ex = []
    for c in combinations(range(1,25), 5):
        if not prim(c): continue
        tot += 1
        if not works(c, n):
            bad += 1
            if len(ex) < 2: ex.append(c)
    print(f"  n={n:>3}  card-5 exhaustive [1,24]: {tot:>7} sets, {bad:>4} failures  {ex if ex else ''}")
