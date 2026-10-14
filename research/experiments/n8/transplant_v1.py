"""Do we have enough to CONSTRUCT deep examples?

Decisive test: transplant the profile.  Take a deep case's reading profile (normalised so the
largest reading = 8), instantiate it at a fresh minimum c by rounding, and measure depth.

If the profile is the cause, depth should survive transplantation.  If it collapses, the profile is
a symptom and the fine arithmetic is the cause.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from math import floor
import statistics as st
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def depth(ds):
    ds=[F(d) for d in ds]
    if min(ds)<=0 or len(set(ds))!=len(ds): return None
    t=TH/min(ds); n=0
    while n<200000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n
        t=max(nextOp(d,t) for d in b); n+=1
    return None
A=[30,74,96,127,159,175,224]      # depth 23
B=[49,205,234,256,286,323,366]    # depth 28
def transplant(base, c):
    r=[F(x,base[0]) for x in base]          # readings relative to d_min
    ds=sorted({int(round(float(c*x))) for x in r})
    return ds if len(ds)==7 else None
for name,base,orig in (("A (depth 23)",A,23), ("B (depth 28)",B,28)):
    print(f"\n  === transplanting profile {name}, original d_min {base[0]} ===")
    res=[]
    for c in range(20,401):
        ds=transplant(base,c)
        if ds is None: continue
        d=depth(ds)
        if d is not None: res.append((d,c,ds))
    ds_=[d for d,_,_ in res]
    print(f"    {len(res)} transplants, c = 20..400")
    print(f"    depth: mean {st.mean(ds_):.2f}  median {st.median(ds_)}  max {max(ds_)}  min {min(ds_)}")
    print(f"    P(depth >= {orig-3}) = {sum(1 for d in ds_ if d>=orig-3)/len(ds_):.4f}")
    print(f"    P(depth >= {orig})   = {sum(1 for d in ds_ if d>=orig)/len(ds_):.4f}")
    top=sorted(res, reverse=True)[:6]
    print(f"    best transplants:")
    for d,c,dd in top:
        print(f"      depth {d:>3} at c = {c:>3}: {dd}  S = {max(dd)/min(dd):.4f}")
    print(f"    exceeds the original ({orig})? "
          f"{'YES -> ' + str(max(ds_)) if max(ds_)>orig else 'no'}")
