"""Cause of depth, at the step level.

lambda_j = (8M+1)/(8M+delta) with delta = s - 8M in (-1,1).  Slow contraction needs LARGE M, or
delta near +1 (the setter just about to leave the bad band).  Deep cascades should therefore show a
different (M, delta) profile from shallow ones.  Measure it.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor
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
def anatomy(ds):
    """per step: (M, delta, lambda) for the winning setter"""
    ds=[F(d) for d in ds]
    if min(ds)<=0 or len(set(ds))!=len(ds): return None
    t=TH/min(ds); out=[]
    for _ in range(200000):
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return out
        tn,s=max((nextOp(d,t),d) for d in b)
        D=1/(8*t); r=s/D; M=round(r/8)
        out.append((int(M), float(r-8*M), float(tn/t)))
        t=tn
    return None
DEEP={"23-move":[30,74,96,127,159,175,224], "28-move":[49,205,234,256,286,323,366],
      "27 banded":[28,69,95,123,154,172,220]}
print("  DEEP CASES -- per-step anatomy\n")
for name,ds in DEEP.items():
    a=anatomy(ds)
    Ms=[x[0] for x in a]; ds_=[x[1] for x in a]; ls=[x[2] for x in a]
    print(f"    {name}: depth {len(a)}")
    print(f"      M      : mean {st.mean(Ms):>6.2f}  median {st.median(Ms):>5}  max {max(Ms):>3}  {Counter(Ms).most_common(5)}")
    print(f"      delta  : mean {st.mean(ds_):>6.3f}  median {st.median(ds_):>6.3f}  frac > 0: {sum(1 for x in ds_ if x>0)/len(ds_):.3f}")
    print(f"      lambda : mean {st.mean(ls):>6.4f}  min {min(ls):.4f}  max {max(ls):.4f}")
print("\n  SHALLOW CASES (depth 1-3) and MID (4-8), sampled\n")
rng=random.Random(4242); buck={}
for _ in range(4000):
    v=speeds(rng.sample(range(1,90),8))
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        a=anatomy(ds)
        if not a: continue
        k="1-3" if len(a)<=3 else ("4-8" if len(a)<=8 else "9+")
        buck.setdefault(k,[]).extend(a)
for k in ("1-3","4-8","9+"):
    if k not in buck: continue
    a=buck[k]; Ms=[x[0] for x in a]; ds_=[x[1] for x in a]; ls=[x[2] for x in a]
    print(f"    depth {k}: {len(a)} steps")
    print(f"      M      : mean {st.mean(Ms):>6.2f}  median {st.median(Ms):>5}  max {max(Ms):>3}  {Counter(Ms).most_common(5)}")
    print(f"      delta  : mean {st.mean(ds_):>6.3f}  median {st.median(ds_):>6.3f}  frac > 0: {sum(1 for x in ds_ if x>0)/len(ds_):.3f}")
    print(f"      lambda : mean {st.mean(ls):>6.4f}  min {min(ls):.4f}  max {max(ls):.4f}")
