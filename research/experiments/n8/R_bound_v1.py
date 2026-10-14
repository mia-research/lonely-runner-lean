"""R bounded is the open problem.  Map it.

Structure: the final scale is D_final = a.g/(8M+1) for the last setter a at lap M, so
    R = d_min/D_final = c(8M+1)/a        (reduced units, c = d_min)
and since a >= c we get  R <= 8M_final + 1.  So R is tied to the LAST lap index.

Three probes:
 (1) verify R = c(8M+1)/a and R <= 8M+1 exactly
 (2) the joint distribution of (R, M_final)
 (3) an adversarial search maximising R, not depth
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random, statistics as st
from collections import Counter
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def run(ds):
    """returns (depth, R, last setter a, last lap M) in reduced units"""
    ds=[F(d) for d in ds]
    if min(ds)<=0 or len(set(ds))!=len(ds): return None
    c=min(ds); t=TH/c; n=0; last=None
    while n<200000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b:
            R=c*8*t
            return (n, R, last)
        D=1/(8*t)
        tn,s=max((nextOp(d,t),d) for d in b)
        M=round(s/D/8)
        last=(s,int(M)); t=tn; n+=1
    return None
print("(1) verify R = c(8M+1)/a and R <= 8M+1")
rng=random.Random(11); ok=0; tot=0; bad=0
for _ in range(3000):
    v=speeds(rng.sample(range(1,90),8))
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        r=run(ds)
        if r is None or r[0]==0: continue
        n,R,(a,M)=r; c=F(min(ds))
        tot+=1
        if R==c*(8*M+1)/a: ok+=1
        if R>8*M+1: bad+=1
print(f"    R = c(8M+1)/a : {ok}/{tot}     R <= 8M+1 violations: {bad}")

print("\n(2) joint distribution of R and the final lap M")
rng=random.Random(77); rows=[]
for _ in range(6000):
    v=speeds(rng.sample(range(1,140),8))
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        r=run(ds)
        if r is None or r[0]==0: continue
        rows.append((float(r[1]), r[2][1], r[0]))
Rs=[x[0] for x in rows]
print(f"    {len(rows)} cascades with depth >= 1")
print(f"    R: min {min(Rs):.4f}  mean {st.mean(Rs):.4f}  max {max(Rs):.4f}")
byM={}
for R,M,d in rows: byM.setdefault(M,[]).append(R)
print(f"    {'M_final':>8} {'n':>7} {'mean R':>9} {'max R':>9} {'8M+1':>6}")
for M in sorted(byM):
    if len(byM[M])<20: continue
    print(f"    {M:>8} {len(byM[M]):>7} {st.mean(byM[M]):>9.4f} {max(byM[M]):>9.4f} {8*M+1:>6}")

print("\n(3) adversarial search maximising R")
def Ronly(ds):
    r=run(ds); return float(r[1]) if r else 0.0
best=(0,None)
rng=random.Random(31415)
for restart in range(200):
    c=rng.randrange(20,80); xs=sorted(rng.sample(range(c+1,int(12*c)),6)); ds=sorted([c]+xs)
    if len(set(ds))!=7: continue
    cur=Ronly(ds); stall=0
    for _ in range(3000):
        w=list(ds); k=rng.randrange(7)
        w[k]+=rng.choice([-4,-3,-2,-1,1,2,3,4])
        if min(w)<=0 or len(set(w))!=7: continue
        w=sorted(w); val=Ronly(w)
        if val>cur: ds,cur,stall=w,val,0
        elif val==cur: ds,stall=w,stall+1
        else: stall+=1
        if stall>500: break
    if cur>best[0]: best=(cur,tuple(ds))
print(f"    max R found: {best[0]:.6f}   {list(best[1])}")
r=run(list(best[1]))
print(f"    depth {r[0]}, last setter {r[2][0]} at lap {r[2][1]}, bound 8M+1 = {8*r[2][1]+1}")
