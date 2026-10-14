"""Two deep families found:
  A  readings spread over [1,8]        gaps ~ 1.5, 0.95, 1.0, 1.14, 0.65, 1.73   (depths 23,27,27)
  B  one small reading, six clustered  gaps ~ 3.41, 0.63, 0.48, 0.66, 0.81, 0.94 (depth 28)
Perturb B the way A was perturbed, and compare the response structure.  All speeds positive."""
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
    while n<40000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n
        t=max(nextOp(d,t) for d in b); n+=1
    return None
B=[49,205,234,256,286,323,366]
A=[30,74,96,127,159,175,224]
for name,BASE in (("FAMILY B (depth 28)",B),("FAMILY A (depth 23)",A)):
    print(f"  {name}  {BASE}\n")
    deltas=list(range(-6,7))
    print(f"    {'d':>5} | " + " ".join(f"{x:>4}" for x in deltas))
    print("    " + "-"*(7+5*len(deltas)))
    for idx,d0 in enumerate(BASE):
        row=[]
        for dl in deltas:
            ds=list(BASE); ds[idx]=d0+dl
            r=depth(ds)
            row.append("  ." if dl==0 else (f"{r:>4}" if r is not None else "   x"))
        print(f"    {d0:>5} | " + " ".join(row))
    print()
print("  scaling control (must be invariant):")
for k in (2,3,5):
    print(f"    B x{k}: {depth([k*x for x in B])}     A x{k}: {depth([k*x for x in A])}")
print()
print("  fine scan of B's minimum at 0.1 resolution (B x10, minimum 460..540):")
REST=[2050,2340,2560,2860,3230,3660]
line=""
prev=None; runs=[]
for c in range(4600,5401,10):
    d=depth([c]+REST)
    if d!=prev:
        runs.append([c/10.0, c/10.0, d]); prev=d
    else: runs[-1][1]=c/10.0
for lo,hi,d in runs:
    print(f"    c in [{lo:>6.1f}, {hi:>6.1f}]  depth {d}")
