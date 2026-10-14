"""Is section 15's Branch-B regularity order-8-specific, or general n?

MANUSCRIPT_v19 section 15 records, for order 8 integer readings with a reading divisible by 8:
   "at least TWO readings always supply a witness, never one and never zero"  [measured, unexplained]

My item-3 middle region (1 <= M <= c-2) is Branch B minus the part SELF covers.  So test the
same statistic at orders 5, 6, 7 -- counting WORKING FLANKS rather than "suppliers", which is
the same object read on the difference set.
"""
from itertools import combinations
import math, collections
def works(ds,e,n):
    M=n*e
    for j in range(e):
        if all(e <= (d*(n*j+1)) % M <= (n-1)*e for d in ds): return True
    return False
for n,HI in ((5,26),(6,20),(7,15),(8,13)):
    k=n-1
    branchB=collections.Counter(); middle=collections.Counter(); ones=[]
    for c in combinations(range(1,HI+1),k):
        g=c[0]
        for x in c[1:]: g=math.gcd(g,x)
        if g!=1: continue
        M=sum(1 for d in c if d%n==0)
        if M < 1: continue                          # Branch B = at least one multiple of n
        w=sum(1 for e in c if works(c,e,n))
        branchB[w]+=1
        if M <= len(c)-2: middle[w]+=1
        if w<=1 and len(ones)<4: ones.append((c,M,w))
    print(f"n={n}  [1,{HI}]")
    print(f"   Branch B (M>=1)      working-flank count: {dict(sorted(branchB.items()))}")
    print(f"   middle (1<=M<=c-2)   working-flank count: {dict(sorted(middle.items()))}")
    print(f"   minimum over Branch B: {min(branchB) if branchB else '-'}"
          f"   {'-> at least two, as the manuscript records at order 8' if branchB and min(branchB)>=2 else '-> NOT at least two'}")
    if ones: print(f"   sets with <=1 working flank: {ones}")
    print()
