# Does (4,5,6) itself survive a wider range, or does the winner count keep shrinking to zero?
# If it fails, no fixed triple works and the '3' is coincidence.  Test [1,24].
from math import gcd
from itertools import combinations
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def works(ds,b):
    for k in range(b):
        if all(clear(a,b,k) for a in ds): return True
    return False
V=24
n=0; bad456=[]; bad246=[]; oneflank=[]
for ds in combinations(range(1,V+1),7):
    if gcd(*ds)!=1: continue
    n+=1
    s=sorted(ds)
    w=[works(ds,s[i]) for i in range(7)]
    if not (w[4] or w[5] or w[6]): bad456.append(ds)
    if not (w[2] or w[4] or w[6]): bad246.append(ds)
    if sum(w)==1: oneflank.append((ds, w.index(True)))
print(f"[1,{V}] exhaustive: {n} primitive sets")
print(f"   triple (4,5,6) fails on {len(bad456)}")
if bad456: print(f"      {bad456[:6]}")
print(f"   triple (2,4,6) fails on {len(bad246)}")
if bad246: print(f"      {bad246[:4]}")
print(f"   sets with exactly ONE working flank: {len(oneflank)}")
from collections import Counter
if oneflank:
    print(f"      its rank: {dict(sorted(Counter(r for _,r in oneflank).items()))}")
    print(f"      sets: {[d for d,_ in oneflank][:6]}")
    lo=[x for x in oneflank if x[1]<4]
    print(f"      any with the unique flank below rank 4: {len(lo)}  {lo[:3]}")
