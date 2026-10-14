"""Is it the ORDER n, or the NUMBER OF BLOCKERS (card - 1)?

At a flank opening of e the disparity e is never blocked, so a set of card m has m-1 blockers.
n=5 full card is 4 -> 3 blockers.  n=6 full card is 5 -> 4 blockers.
Collapsed data already shows card-4 sets at n=6 all work at rank 1.

Grid: for each order n and each card m, does the LARGEST disparity always host a lonely opening?
If failures appear exactly when m-1 >= 4 regardless of n, the split is about blocker COUNT and
n=5 is special only because it cannot have four blockers.
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

print("cell = (#failures, #sets);  '.' = no failures;  m = card, blockers = m-1")
print(f"{'n':>3} | " + " ".join(f"{'m='+str(m):>16}" for m in range(2, 9)))
for n in range(5, 10):
    row = []
    for m in range(2, 9):
        if m > n - 1:
            row.append(f"{'-':>16}"); continue
        hi = {2: 120, 3: 60, 4: 34, 5: 24, 6: 18, 7: 15, 8: 13}[m]
        tot = bad = 0; ex = None
        for c in combinations(range(1, hi+1), m):
            if not prim(c): continue
            tot += 1
            if not works(c, n):
                bad += 1
                if ex is None: ex = c
        cell = f"{'.':>7}({tot})" if bad == 0 else f"{bad:>7}({tot})"
        row.append(f"{cell:>16}")
    print(f"{n:>3} | " + " ".join(row))
print()
print("first failing example per (n, m):")
for n in range(5, 10):
    for m in range(2, min(9, n)):
        hi = {2: 120, 3: 60, 4: 34, 5: 24, 6: 18, 7: 15, 8: 13}[m]
        for c in combinations(range(1, hi+1), m):
            if prim(c) and not works(c, n):
                print(f"   n={n} card={m} blockers={m-1}:  {c}")
                break
        else:
            print(f"   n={n} card={m} blockers={m-1}:  none")
