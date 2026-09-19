"""If every mover has denominator q <= n-1, then k = lcm(q_i) - 1 is CLEAR.
Reason: k ≡ -1 (mod q_i) for every i, and last_class_forces says that class is blocked
only by p=1,q=n.  So the exhaustive 'no shadowing at q <= n-1' is a theorem, for any
number of movers and any n -- not a table."""
from math import gcd, lcm
from itertools import combinations_with_replacement
import random
def blocks(p,A,q,n): 
    M=n*q; r=(p*A)%M; return min(r,M-r)<q
bad=0; tot=0
for n in range(3,14):
    pool=[(p,q) for q in range(2,n) for p in range(1,q) if gcd(p,q)==1]   # q <= n-1
    for _ in range(4000):
        m=[random.choice(pool) for _ in range(random.randint(2,max(2,n-2)))]
        L=lcm(*[q for _,q in m]); k=L-1; tot+=1
        if any(blocks(p,n*k+1,q,n) for p,q in m): bad+=1
print(f"random mover sets, q <= n-1, n=3..13:  k = lcm-1 clear in {tot-bad}/{tot} "
      f"({'HOLDS' if bad==0 else f'FAILS {bad}'})")
# exhaustive at n=8, six movers, q<=7 -- the case the table covered
pool7=[(p,q) for q in range(2,8) for p in range(1,q) if gcd(p,q)==1]
bad2=0; tot2=0
for m in combinations_with_replacement(pool7,6):
    L=lcm(*[q for _,q in m]); k=L-1; tot2+=1
    if any(blocks(p,8*k+1,q,8) for p,q in m): bad2+=1
print(f"exhaustive n=8, six movers q<=7: k = lcm-1 clear in {tot2-bad2}/{tot2} "
      f"({'HOLDS' if bad2==0 else f'FAILS {bad2}'})")
print("\nthe earlier 'best' q<=7 set, ((1,2),(1,3),(4,5),(5,6),(2,7),(3,7)), L=210:")
m=((1,2),(1,3),(4,5),(5,6),(2,7),(3,7))
unc=[k for k in range(210) if not any(blocks(p,8*k+1,q,8) for p,q in m)]
print(f"   uncovered k = {unc};  209 = lcm-1 present: {209 in unc}")
