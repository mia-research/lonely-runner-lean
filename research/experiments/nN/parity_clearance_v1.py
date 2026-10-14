"""Does the largest-flank clearance threshold f(k) coincide with the covering threshold 2k+1?

f(k) = least order n at which NO difference set of card k+1 (k blockers) fails the largest flank.
The manuscript's proved row is `ManyDifferences.stops_when_twice_card_lt`: k differences stop at
every n > 2k, i.e. n >= 2k+1 -- and 2k+1 is ODD.

Earlier measurement (narrow ranges): f(3)=5, f(4)=8, f(5)=11, f(6)=13 against 2k+1 = 7,9,11,13.
Re-measured here with wider ranges, and with the gcd(d,n) cage recorded alongside, since the cage
is the manuscript's parity mechanism (Thm 4.13): an offset sharing a factor with n is confined to
[gcd/n, 1-gcd/n] and can never bind.
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

RANGE = {3: 34, 4: 26, 5: 20, 6: 16, 7: 14}
print(f"{'k':>3} {'card':>5} {'2k+1':>5} {'f(k)':>5} {'match?':>7}   failures by n")
for k in (3, 4, 5, 6, 7):
    card = k + 1; hi = RANGE[k]
    sets = [c for c in combinations(range(1, hi+1), card) if prim(c)]
    fails = {}
    for n in range(max(4, card), 2*k + 6):
        fails[n] = sum(1 for c in sets if not works(c, n))
    f = None
    for n in sorted(fails):
        if all(fails[m] == 0 for m in sorted(fails) if m >= n): f = n; break
    shown = " ".join(f"{n}:{v}" for n, v in sorted(fails.items()) if v) or "(none)"
    print(f"{k:>3} {card:>5} {2*k+1:>5} {str(f):>5} {str(f == 2*k+1):>7}   {shown}")

print()
print("=== the cage, Thm 4.13: fraction of offsets that can never bind at a grid instant ===")
print(f"{'n':>3} {'parity':>7} {'caged offsets (gcd(d,n)>1)':>28} {'share':>7}")
for n in range(5, 15):
    caged = [d for d in range(1, n) if math.gcd(d, n) > 1]
    print(f"{n:>3} {'even' if n%2==0 else 'odd':>7} {str(caged):>28} {len(caged)}/{n-1} = {len(caged)/(n-1):.3f}")
