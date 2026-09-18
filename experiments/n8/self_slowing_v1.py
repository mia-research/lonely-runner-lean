"""Mechanism hypothesis: the cascade SELF-SLOWS.  As the scale contracts, every reading inflates, so
blockers are caught at higher lap index M, and lambda = (8M+1)/(8M+delta) -> 1.  Depth is large when
this slowdown sets in before clearance.

Two tests:
 (A) does M increase ALONG a cascade?  (trace the M sequence of the deep cases)
 (B) is lambda < 9/7 always?  (the M=1 maximum -- an exact bound if so)
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor
import random, statistics as st
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def anat(ds):
    ds=[F(d) for d in ds]; t=TH/min(ds); out=[]
    for _ in range(200000):
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return out
        tn,s=max((nextOp(d,t),d) for d in b)
        D=1/(8*t); r=s/D; M=round(r/8)
        out.append((int(M), float(tn/t)))
        t=tn
    return out
print("(A) the M sequence along each deep cascade\n")
for name,ds in (("23-move",[30,74,96,127,159,175,224]),
                ("28-move",[49,205,234,256,286,323,366]),
                ("27 banded",[28,69,95,123,154,172,220])):
    a=anat(ds); Ms=[x[0] for x in a]
    print(f"  {name} (depth {len(a)}):")
    print(f"    M: {Ms}")
    h=len(Ms)//2
    print(f"    mean M first half {st.mean(Ms[:h]):.2f}   second half {st.mean(Ms[h:]):.2f}"
          f"   -> {'INCREASES' if st.mean(Ms[h:])>st.mean(Ms[:h]) else 'does not increase'}")
    ls=[x[1] for x in a]
    print(f"    mean lambda first half {st.mean(ls[:h]):.4f}   second half {st.mean(ls[h:]):.4f}\n")
print("(B) is lambda < 9/7 = 1.285714... always?")
rng=random.Random(31337); mx=0; n=0; viol=0; arg=None
for _ in range(6000):
    v=speeds(rng.sample(range(1,120),8))
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        for M,l in anat(ds):
            n+=1
            if l>mx: mx,arg=l,(M,ds)
            if l>=9/7: viol+=1
print(f"    {n} steps sampled")
print(f"    max lambda observed : {mx:.9f}   (9/7 = {9/7:.9f})")
print(f"    steps with lambda >= 9/7 : {viol}")
print(f"    the maximiser had M = {arg[0]}")
print(f"\n    algebra: lambda = (8M+1)/(8M+delta) with delta > -1, so lambda < (8M+1)/(8M-1),")
print(f"             which is largest at M = 1, giving 9/7.  M >= 1 since d_min never blocks.")
