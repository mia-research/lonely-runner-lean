"""Two questions the framework has never been asked.

Q1  WHICH disparity supplies the instant?  Thm 6.2(d) says SOME runner sits at exactly 1/8 at the
    fixed point -- the flank.  Nobody has measured WHICH.  If it is determined by the arrangement,
    the construction becomes deterministic in the flank too, not just the scale.

Q2  WHICH BLOCKING GRAPHS OCCUR?  At an instant the in-the-way pairs form an undirected graph on
    the 8 runners (Doors sec5, inWay_comm).  Cor 4.4 says the independent set is never exactly 7.
    Nobody has asked what ELSE is forbidden.  Proved-and-idle objects: sum_blockDegree,
    blockDegree_symm_pairs, lonelyAt_iff_blockDegree_zero.
Exact Fraction."""
import random
from fractions import Fraction as F
from math import floor
from collections import Counter
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def cascade(ds,cap=4000):
    m=min(ds); t=TH/m; n=0
    while n<cap:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return t,n
        t=max(nextOp(d,t) for d in b); n+=1
    return None,0

print("=== Q1: which disparity is the flank at the fixed point? ===")
rng=random.Random(4); rank=Counter(); ratio=[]; nflank=Counter()
for _ in range(4000):
    v=sorted(rng.sample(range(0,90),8))
    for i in range(8):
        ds=sorted(abs(v[j]-v[i]) for j in range(8) if j!=i)
        t,n=cascade([F(d) for d in ds])
        if t is None: continue
        hits=[r for r,d in enumerate(ds,1) if circd(F(d)*t)==TH]
        nflank[len(hits)]+=1
        for r in hits:
            rank[r]+=1
            ratio.append(float(F(ds[r-1])/min(ds)))
tot=sum(rank.values())
print(f"   flank rank (1 = smallest disparity, 7 = largest): ")
for r in sorted(rank): print(f"      rank {r}: {rank[r]:7d}  ({rank[r]/tot:.4f})")
print(f"   how many runners sit at EXACTLY 1/8 at the fixed point: {dict(sorted(nflank.items()))}")
import statistics as st
print(f"   flank/d_min ratio: mean {st.mean(ratio):.3f}  median {st.median(ratio):.3f}  max {max(ratio):.1f}")

print()
print("=== Q2: which blocking graphs occur? ===")
rng=random.Random(9)
lonely=Counter(); edges=Counter(); degseq=set()
for _ in range(2500):
    v=sorted(rng.sample(range(1,60),8))
    ds=[F(x) for x in v]
    for _ in range(40):
        t=F(rng.randint(1,4000),997)
        E=[(a,b) for a in range(8) for b in range(a+1,8) if circd((ds[b]-ds[a])*t)<TH]
        deg=[0]*8
        for a,b in E: deg[a]+=1; deg[b]+=1
        lonely[sum(1 for d in deg if d==0)]+=1
        edges[len(E)]+=1
        degseq.add(tuple(sorted(deg)))
print(f"   simultaneously lonely runners: {dict(sorted(lonely.items()))}")
print(f"     (Cor 4.4: never exactly 7 -> observed 7 count = {lonely.get(7,0)})")
e=sorted(edges)
print(f"   blocking pairs out of 28: min {e[0]}  max {e[-1]}  mean {sum(k*c for k,c in edges.items())/sum(edges.values()):.2f}")
print(f"   distinct degree sequences seen: {len(degseq)}")
odd=[d for d in degseq if sum(d)%2]
print(f"   degree sequences with odd sum (impossible in a graph): {len(odd)}")
print(f"   max degree ever seen: {max(max(d) for d in degseq)} of 7")
