"""Family B's depth-28 cell (width 0.2) sits inside a cluster of 22-24 cells.  Family A's depth-23
cell (width 0.6) sits alone among 18s.  Deeper = narrower, and the deepest sits INSIDE a high
neighbourhood.

TEST: is the structure NESTED?  Zoom into the deepest cell at successively finer resolution and ask
whether deeper cells appear inside.  If they do, depth is unbounded along this axis and deep cases
are constructible by recursive zooming.  All speeds positive."""
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
REST=[205,234,256,286,323,366]
def cells(lo, hi, steps):
    """enumerate cells of depth over [lo,hi] using `steps` samples"""
    out=[]; prev=None
    for i in range(steps+1):
        c=lo+(hi-lo)*F(i,steps)
        d=depth([c]+[F(r) for r in REST])
        if d!=prev: out.append([c,c,d]); prev=d
        else: out[-1][1]=c
    return out
lo,hi=F(488,10),F(492,10)      # around the depth-28 cell
for level,steps in ((1,400),(2,4000)):
    cs=cells(lo,hi,steps)
    best=max((d for _,_,d in cs if d is not None), default=None)
    print(f"  zoom level {level}: [{float(lo):.6f}, {float(hi):.6f}], {steps} samples, {len(cs)} cells, max depth {best}")
    for a,b,d in cs:
        if d is not None and d>=26:
            print(f"      depth {d:>4} on [{float(a):.6f}, {float(b):.6f}]  width {float(b-a):.6f}")
    # narrow to the deepest cell for the next zoom
    deep=[(a,b,d) for a,b,d in cs if d==best]
    if deep:
        a,b,_=deep[0]
        pad=(b-a)/2 if b>a else F(1,1000)
        lo,hi=a-pad,b+pad
print()
print("  same probe on FAMILY A's depth-23 cell for comparison:")
REST=[74,96,127,159,175,224]
cs=cells(F(2985,100),F(3046,100),3000)
best=max((d for _,_,d in cs if d is not None), default=None)
print(f"    [29.85, 30.46], 3000 samples, {len(cs)} cells, max depth {best}")
for a,b,d in cs:
    if d is not None and d>=23:
        print(f"      depth {d:>4} on [{float(a):.6f}, {float(b):.6f}]  width {float(b-a):.6f}")
