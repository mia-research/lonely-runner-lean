"""Untested axis: is the cell decomposition SEPARABLE?  If cells are boxes (products of intervals),
depth factorises coordinate-wise and the 1-D censuses compose.  If they are sheared, it does not.

Map a 2-D slice: vary the minimum c and one other disparity on a grid, print the depth field.
All speeds positive."""
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
SYM=" 123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ"
def cell(d): return "." if d==0 else (SYM[d] if d is not None and d<len(SYM) else "*")
BASE=[30,74,96,127,159,175,224]
# axis 0 = minimum (28.0 .. 32.0), axis 6 = the largest (215 .. 232)
print("  depth field.  rows: largest disparity 215..232 (step 0.5); cols: minimum 28.0..32.0 (step 0.05)")
print("  '.' = depth 0,  digits/letters = depth,  '*' = >35\n")
rows=[]
for big10 in range(4300, 4641, 10):          # 215.0 .. 232.0 step 0.5
    big=F(big10,20)
    line=""
    for c100 in range(2800, 3201, 5):        # 28.00 .. 32.00 step 0.05
        c=F(c100,100)
        ds=[c]+BASE[1:6]+[big]
        line += cell(depth(ds))
    rows.append((float(big), line))
print("        " + "28.0" + " "*(len(rows[0][1])-9) + "32.0")
for b,l in rows:
    print(f"  {b:>6.1f} {l}")
print()
# separability check: does the depth-23 region form a rectangle?
pts=[(b,i) for b,l in rows for i,ch in enumerate(l) if ch==SYM[23]]
if pts:
    bs=sorted({p[0] for p in pts}); cs=sorted({p[1] for p in pts})
    full=len(bs)*len(cs)
    print(f"  depth-23 cells: {len(pts)} grid points, bounding box {len(bs)} x {len(cs)} = {full}")
    print(f"  fill fraction of the bounding box: {len(pts)/full:.4f}   -> {'BOX (separable)' if len(pts)==full else 'NOT a box (sheared)'}")
