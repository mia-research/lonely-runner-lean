"""Transplanting a profile reproduces its depth but never exceeds it.  Two families exist, so the
untested axis is the PATH BETWEEN THEM.

Interpolate p(u) = (1-u).A + u.B in reading space (both normalised so d_min reads 1), instantiate
at a large c so rounding is fine, and walk u from 0 to 1.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from math import floor
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
A=[30,74,96,127,159,175,224]; B=[49,205,234,256,286,323,366]
pa=[F(x,A[0]) for x in A]; pb=[F(x,B[0]) for x in B]
C=3000
def inst(p):
    ds=sorted({int(round(float(C*x))) for x in p})
    return ds if len(ds)==7 else None
print(f"  interpolating A -> B in reading space, instantiated at c = {C}\n")
print(f"  {'u':>6} {'depth':>6} {'S':>8}   readings (d_min = 1)")
best=(0,None,None)
for i in range(0,101):
    u=F(i,100)
    p=[(1-u)*a+u*b for a,b in zip(pa,pb)]
    ds=inst(p)
    if ds is None: continue
    d=depth(ds)
    if d is None: continue
    if d>best[0]: best=(d,float(u),ds)
    if i%5==0 or d>28:
        print(f"  {float(u):>6.2f} {d:>6} {max(ds)/min(ds):>8.4f}   " +
              " ".join(f"{x/ds[0]:.2f}" for x in ds))
print(f"\n  best along the path: depth {best[0]} at u = {best[1]}")
print(f"    {best[2]}")
print(f"    exceeds both endpoints (23, 28)? {'YES' if best[0]>28 else 'no'}")
