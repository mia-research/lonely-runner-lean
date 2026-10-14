"""Is the driver 'n divides some d' (already a framework theorem) or the strictly weaker
'some d shares a factor with n'?

`LRC.SpecN.lonelyAt_inv_of_not_dvd` PROVES: if n divides no disparity, the subject is lonely at
1/n.  That is an instant, not necessarily an opening of the largest flank.  My empirical finding
was about gcd(d,n) > 1, which is a WEAKER hypothesis to violate (more sets are 'resonant').
Do sets that are resonant but contain NO multiple of n ever fail the largest flank?
If yes, the gcd condition is the real driver and is strictly stronger than the divisibility one.
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

RANGE = {5: 22, 6: 16, 7: 14}
print("failures split by which condition they violate")
print(f"{'n':>3} {'card':>5} {'fail w/ mult of n':>18} {'fail: gcd>1 but NO mult of n':>30}")
mid = 0
for n in range(6, 13):
    for card in (5, 6, 7):
        if card > n - 1: continue
        hi = RANGE[card]
        a = b = 0
        ex = None
        for c in combinations(range(1, hi+1), card):
            if not prim(c): continue
            if works(c, n): continue
            if any(d % n == 0 for d in c): a += 1
            else:
                b += 1
                if ex is None: ex = c
        if a or b:
            mid += b
            print(f"{n:>3} {card:>5} {a:>18} {b:>30}" + (f"   e.g. {ex}" if ex else ""))
print()
print(f"failures that are resonant but contain no multiple of n: {mid}")
print("if > 0, the gcd condition is the real driver, strictly stronger than n | d.")
