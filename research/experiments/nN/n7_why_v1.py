"""WHY do the 119 fail?  Causal test plus per-blocker trace.

At order 7 every failure contains a multiple of 7 (7 is prime, and the non-resonant case is
PROVED lonely at 1/7).  Is the 7-multiple the cause?  Direct test: delete it and re-check.

Note the algebra.  For d = 7m the factor cancels: the reading at flank e, opening j is
     7m(7j+1)/(7e) = m(7j+1)/e,
so a 7-multiple is read at the SMALLER value m -- it behaves like a disparity of size m against
the flank, not of size 7m.  That is the candidate mechanism.
"""
import math
from itertools import combinations
from collections import Counter

def works_at(c, e, n=7):
    M = n*e; lo, hi = e, (n-1)*e
    return any(all(lo <= (d*(n*j+1)) % M <= hi for d in c) for j in range(e))

def blocked_count(d, e, n=7):
    M = n*e; lo, hi = e, (n-1)*e
    return sum(1 for j in range(e) if not (lo <= (d*(n*j+1)) % M <= hi))

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

hi = 18
sets = [c for c in combinations(range(1, hi+1), 6) if prim(c)]
fails = [c for c in sets if any(d % 7 == 0 for d in c) and not works_at(c, c[-1])]
print(f"order 7, card 6, [1,{hi}]: {len(fails)} failures\n")

fixed_by_removing_7mult = 0
fixed_by_removing_other = Counter()
for c in fails:
    e = c[-1]
    sevens = [d for d in c if d % 7 == 0]
    # remove each 7-multiple (that is not the flank) and retest
    for s in sevens:
        if s == e: continue
        c2 = tuple(d for d in c if d != s)
        if works_at(c2, c2[-1]): fixed_by_removing_7mult += 1; break
    # for contrast: remove a NON-multiple and retest
    for s in c[:-1]:
        if s % 7 == 0: continue
        c2 = tuple(d for d in c if d != s)
        if works_at(c2, c2[-1]): fixed_by_removing_other[s] += 1; break

print(f"failures fixed by deleting a 7-multiple : {fixed_by_removing_7mult} / {len(fails)}")
print(f"failures fixed by deleting a non-multiple: {sum(fixed_by_removing_other.values())} / {len(fails)}")
print()
print("=== per-blocker blocked counts at the largest flank (generic count is 2e/7) ===")
print(f"{'set':>26} {'e':>4} {'2e/7':>6}  per-blocker (d: blocked)  [* = multiple of 7]")
for c in fails[:12]:
    e = c[-1]
    row = "  ".join(f"{d}{'*' if d%7==0 else ''}:{blocked_count(d,e)}" for d in c[:-1])
    print(f"{str(c):>26} {e:>4} {2*e/7:>6.2f}  {row}")
print()
print("=== does the 7-multiple block MORE than generic? ===")
ratios_7 = []; ratios_o = []
for c in fails:
    e = c[-1]
    for d in c[:-1]:
        r = blocked_count(d, e) * 7 / (2 * e)
        (ratios_7 if d % 7 == 0 else ratios_o).append(r)
if ratios_7:
    print(f"  7-multiples : n={len(ratios_7):>4}  mean ratio {sum(ratios_7)/len(ratios_7):.3f}  max {max(ratios_7):.3f}")
print(f"  others      : n={len(ratios_o):>4}  mean ratio {sum(ratios_o)/len(ratios_o):.3f}  max {max(ratios_o):.3f}")
