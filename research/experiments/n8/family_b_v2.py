"""family_b_v1's fine scan was buggy: I scanned c over the raw 4600..5400 while REST was already
scaled x10, so c was never the minimum and every configuration read depth 0.  Corrected here.

Compare the CELL STRUCTURE of the two families at 0.1 resolution.  All speeds positive."""
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
def scan(REST, lo10, hi10, label):
    print(f"  {label}  (0.1 resolution, minimum from {lo10/10} to {hi10/10})")
    runs=[]; prev=None
    for c10 in range(lo10, hi10+1):
        d=depth([F(c10,10)]+[F(r) for r in REST])
        if d!=prev: runs.append([c10/10.0, c10/10.0, d]); prev=d
        else: runs[-1][1]=c10/10.0
    for lo,hi,d in runs:
        w=hi-lo+0.1
        print(f"     [{lo:>7.1f}, {hi:>7.1f}]  width {w:>5.1f}  depth {d}")
    print(f"     -> {len(runs)} cells\n")
scan([205,234,256,286,323,366], 440, 560, "FAMILY B, minimum around 49")
scan([74,96,127,159,175,224],   250, 330, "FAMILY A, minimum around 30")
print("  the two families' response to perturbing d_min, side by side:")
print("     A: a narrow spike (depth 23 on a plateau of 18s, cell width ~0.57)")
print("     B: a broad high region -- see the widths above")
