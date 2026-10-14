"""Map depth via the cell decomposition.  Along the c (minimum) axis, enumerate EVERY cell by
bisecting each transition, and record (interval, width, depth).  Then ask what width says about
depth.  All speeds positive."""
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
def depth(c,REST):
    ds=[F(c)]+[F(r) for r in REST]
    if min(ds)<=0 or len(set(ds))!=len(ds): return None
    t=TH/min(ds); n=0
    while n<40000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n
        t=max(nextOp(d,t) for d in b); n+=1
    return None
def census(REST, lo, hi, step=F(1,20), bis=45):
    cells=[]; c=F(lo); d=depth(c,REST); start=c
    while c<hi:
        c2=c+step; d2=depth(c2,REST)
        if d2!=d:
            L,H=c,c2
            for _ in range(bis):
                M=(L+H)/2
                if depth(M,REST)==d: L=M
                else: H=M
            cells.append((start,H,d)); start=H; d=d2
        c=c2
    cells.append((start,F(hi),d))
    return cells
REST=[74,96,127,159,175,224]
cells=census(REST, 20, 60)
print(f"  {len(cells)} cells over c in [20, 60]   (six other disparities fixed)\n")
print(f"  {'cell':>28} {'width':>10} {'depth':>6}")
for a,b,d in cells:
    print(f"  [{float(a):>10.5f}, {float(b):>10.5f}] {float(b-a):>10.5f} {str(d):>6}")
print()
byd={}
for a,b,d in cells:
    if d is None: continue
    byd.setdefault(d,[]).append(float(b-a))
print(f"  {'depth':>6} {'cells':>6} {'total width':>12} {'mean width':>11}")
for d in sorted(byd):
    w=byd[d]
    print(f"  {d:>6} {len(w):>6} {sum(w):>12.5f} {st.mean(w):>11.5f}")
tot=sum(sum(w) for w in byd.values())
print(f"\n  measure-weighted depth distribution over c in [20,60]:")
for d in sorted(byd):
    print(f"    depth {d:>3}: {sum(byd[d])/tot:.4f} of the range")
