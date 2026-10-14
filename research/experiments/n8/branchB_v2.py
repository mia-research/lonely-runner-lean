"""8-periodicity (Guard.block_periodic) means only [1,7] matters for integer readings, and the joint
uncovered is exactly twice it.  Use that to push Branch B's range far past 40.

Target: is  min { uncovered([1,7]) : integer profile containing a multiple of 8 }  bounded below?
Search by integer hill-climbing, readings up to 200."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from itertools import combinations
import random
def unc17(S):
    bad=[]
    for s in S:
        k=0
        while F(8*k-1,1)/s <= 8:
            a,b=F(8*k-1,1)/s, F(8*k+1,1)/s
            if b>1 and a<7: bad.append((max(a,F(1)),min(b,F(7))))
            k+=1
    bad.sort(); merged=[]
    for a,b in bad:
        if merged and a<=merged[-1][1]: merged[-1]=(merged[-1][0],max(merged[-1][1],b))
        else: merged.append((a,b))
    u=F(6)
    for a,b in merged: u-=(b-a)
    return u
# sanity: the minimiser halves
print(f"  check: [3,4,5,7,11,24] uncovered([1,7]) = {unc17([F(x) for x in [3,4,5,7,11,24]])}"
      f"  (joint was 53/462, half = {F(53,924)})")
print()
rng=random.Random(31415)
best=(F(10),None)
for HI in (40, 80, 200):
    b=(F(10),None)
    for restart in range(3000):
        m8=rng.choice([x for x in range(8,HI+1,8)])
        others=sorted(rng.sample([x for x in range(2,HI+1) if x!=m8], 5))
        prof=sorted(others+[m8])
        cur=unc17([F(x) for x in prof]); stall=0
        for _ in range(900):
            w=list(prof); k=rng.randrange(6)
            w[k]+=rng.choice([-3,-2,-1,1,2,3])
            if w[k]<2 or w[k]>HI or len(set(w))!=6: continue
            w=sorted(w)
            if not any(x%8==0 for x in w): continue
            v=unc17([F(x) for x in w])
            if v<cur: prof,cur,stall=w,v,0
            elif v==cur: prof,stall=w,stall+1
            else: stall+=1
            if stall>150: break
        if cur<b[0]: b=(cur,tuple(prof))
    print(f"  readings <= {HI:>3}: min uncovered([1,7]) = {b[0]} = {float(b[0]):.10f}   at {list(b[1])}")
    if b[0]<best[0]: best=b
print()
print(f"  overall minimum found: {best[0]} = {float(best[0]):.10f}  at {list(best[1])}")
print(f"  joint (doubled): {2*best[0]} = {float(2*best[0]):.10f}")
print(f"  any zero? {best[0]==0}")
