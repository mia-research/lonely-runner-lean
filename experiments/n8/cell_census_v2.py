"""Census cells along EVERY axis, for both known deep cases, and test the width-depth relation.

Along axis i we vary disparity a_i over a range and enumerate cells by bisection.  Each cell is a
maximal interval of constant depth.  Question: is cell width related to depth, and how?
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from math import floor, log
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
    while n<40000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n
        t=max(nextOp(d,t) for d in b); n+=1
    return None
def census_axis(base, i, lo, hi, step, bis=40):
    def dep(x):
        ds=list(base); ds[i]=x; return depth(ds)
    cells=[]; c=F(lo); d=dep(c); start=c
    while c<hi:
        c2=c+step; d2=dep(c2)
        if d2!=d:
            L,H=c,c2
            for _ in range(bis):
                M=(L+H)/2
                if dep(M)==d: L=M
                else: H=M
            cells.append((float(H-start), d)); start=H; d=d2
        c=c2
    cells.append((float(F(hi)-start), d))
    return cells
CASES={
 "23-move [30,74,96,127,159,175,224]": [30,74,96,127,159,175,224],
 "28-move [43,106,163,216,270,313,366]": [43,106,163,216,270,313,366],
}
allcells=[]
for name,base in CASES.items():
    tot=0
    for i,v in enumerate(base):
        lo=max(1, v*0.55); hi=v*1.6
        cs=census_axis(base,i,lo,hi,F(int(max(1,(hi-lo)/60)*100),100) if hi-lo>60 else F(1,20))
        allcells += [(w,d) for w,d in cs if d is not None]
        tot += len(cs)
    print(f"  {name}: depth {depth(base)},  {tot} cells across its 7 axes")
print(f"\n  total cells: {len(allcells)}")
byd={}
for w,d in allcells: byd.setdefault(d,[]).append(w)
print(f"\n  {'depth':>6} {'cells':>7} {'mean width':>12} {'median':>10} {'max':>10}")
for d in sorted(byd):
    if len(byd[d])<3: continue
    w=byd[d]
    print(f"  {d:>6} {len(w):>7} {st.mean(w):>12.4f} {st.median(w):>10.4f} {max(w):>10.4f}")
pairs=[(d,w) for w,d in allcells if d>0 and w>0]
xs=[float(d) for d,w in pairs]; ys=[log(w) for d,w in pairs]
mx,my=st.mean(xs),st.mean(ys)
cov=sum((a-mx)*(b-my) for a,b in zip(xs,ys))/len(xs)
print(f"\n  correlation(depth, log width) over {len(pairs)} cells with depth>=1: "
      f"{cov/(st.pstdev(xs)*st.pstdev(ys)):+.4f}")
slope=cov/st.pvariance(xs)
print(f"  regression: log(width) = {my-slope*mx:.3f} + {slope:.4f} * depth")
print(f"  i.e. each extra unit of depth multiplies cell width by {2.718281828**slope:.4f}")
