"""The n=5 residue: resonant AND wide ratio.  What is its structure?

The prime theorem needs 5 to divide no disparity.  For d = 5m the algebra is different:
     5m*(5j+1)/(5e) = m*(5j+1)/e,
so a 5-multiple is read at m against modulus e, and is clear iff  m(5j+1) mod e in [e/5, 4e/5].
At the prime theorem's own j (where 5j+1 = e*s) this residue is 0 -- so the 5-multiple is exactly
what blocks there.  The residue class therefore needs a different opening, and the question is
whether its structure is simpler than the general problem.
"""
import math
from itertools import combinations
from collections import Counter

def works_at(c, e, n=5):
    M = n*e; lo, hi = e, (n-1)*e
    return any(all(lo <= (d*(n*j+1)) % M <= hi for d in c) for j in range(e))

def prim(c):
    g = c[0]
    for x in c[1:]: g = math.gcd(g,x)
    return g == 1

hi = 60
nmult = Counter(); flank5 = Counter(); tight = []
tot = 0
for c in combinations(range(1, hi+1), 4):
    if not prim(c): continue
    e = c[-1]
    if all(d % 5 != 0 for d in c): continue     # proved: non-resonant
    if e <= 4 * c[0]: continue                  # proved: ratio condition
    tot += 1
    nmult[sum(1 for d in c if d % 5 == 0)] += 1
    flank5[e % 5 == 0] += 1
    # how many openings work?  tight = exactly one
    M = 5*e; lo, up = e, 4*e
    w = sum(1 for j in range(e) if all(lo <= (d*(5*j+1)) % M <= up for d in c))
    if w <= 1: tight.append((c, w))
print(f"n=5 residue (resonant AND wide ratio), [1,{hi}]: {tot} sets")
print(f"   number of 5-multiples in the set : {dict(sorted(nmult.items()))}")
print(f"   is the LARGEST a multiple of 5?  : {dict(flank5)}")
print(f"   tight (<=1 working opening)      : {len(tight)}")
if tight:
    print(f"   max element among tight          : {max(max(c) for c,_ in tight)}")
    zero = [c for c,w in tight if w == 0]
    print(f"   with ZERO openings               : {len(zero)}")
    print(f"   tight sets: {[c for c,_ in tight][:20]}")
