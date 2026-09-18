"""A scale D fails for a subject iff some disparity d reads within 1 of a multiple of 8:
   |d/D - 8M| < 1  <=>  D in ( d/(8M+1), d/(8M-1) ),  M >= 1,   plus D > d_min (the M=0 case).
So the BAD scales are an explicit union of open intervals in ONE dimension, and the good scales
are its gaps.  The left endpoints d/(8M+1) are exactly the flank openings in scale form.

CLAIM TO TEST: the cascade's answer is the LARGEST left endpoint at or below d_min that lies
outside every bad interval.  If so the procedure is: sort <=7K candidate scales, walk down, take
the first clear one -- finite, explicit, and it NAMES the scale.  Exact Fraction."""
import random
from fractions import Fraction as F
from math import floor
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def clear_at_scale(ds,D):
    return all(circd(F(d)/(8*D))>=TH for d in ds)   # t = 1/(8D); reading d/D
def cascade_scale(ds,cap=5000):
    m=min(ds); t=TH/m; n=0
    while n<cap:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return F(1)/(8*t), n
        nx=[]
        for d in b:
            k=floor(d*t-TH)
            while F(k)+TH < d*t: k+=1
            if k<0: k=0
            nx.append((F(k)+TH)/d)
        t=max(nx); n+=1
    return None,n
def endpoint_walk(ds,KMAX=400):
    """largest D <= d_min of the form d/(8M+1) that is clear"""
    m=min(ds)
    cands=set()
    for d in ds:
        for M in range(0,KMAX+1):
            D=F(d,8*M+1)
            if D<=m: cands.add(D)
    for D in sorted(cands,reverse=True):
        if clear_at_scale(ds,D): return D
    return None

rng=random.Random(2026)
agree=0; tot=0; worstidx=0
print("checking: cascade's final scale == largest clear endpoint d/(8M+1) below d_min")
for _ in range(4000):
    v=sorted(rng.sample(range(0,90),8))
    for i in range(8):
        ds=sorted(abs(v[j]-v[i]) for j in range(8) if j!=i)
        Dc,n=cascade_scale([F(d) for d in ds])
        if Dc is None: continue
        De=endpoint_walk(ds)
        tot+=1
        if De==Dc: agree+=1
        else:
            if worstidx<3:
                print(f"   MISMATCH ds={ds}  cascade {Dc}  endpoint {De}")
                worstidx+=1
print(f"   {agree} of {tot} agree exactly  ({agree/tot:.6f})")

print()
print("how many candidate scales does the walk actually have to test?")
rng=random.Random(7)
import statistics as st
need=[]
for _ in range(2000):
    v=sorted(rng.sample(range(0,90),8))
    for i in range(8):
        ds=sorted(abs(v[j]-v[i]) for j in range(8) if j!=i)
        m=min(ds)
        cands=sorted({F(d,8*M+1) for d in ds for M in range(0,60) if F(d,8*M+1)<=m},reverse=True)
        for r,D in enumerate(cands,1):
            if clear_at_scale(ds,D): need.append(r); break
print(f"   rank of the winning candidate: mean {st.mean(need):.2f}  median {st.median(need)}  max {max(need)}")
