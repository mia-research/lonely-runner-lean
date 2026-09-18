"""The 2-D map shows the depth-23 region is a perfect box, but the depth-0 boundary is DIAGONAL.
Claim: walls are HOMOGENEOUS -- of the form q.a_i = p.a_j with q = 8N+-1, p = 8M+-1 -- because the
whole structure is scale-invariant.  In a (c, big) slice that gives:
    vertical lines   (walls pairing c with a fixed disparity)
    horizontal lines (walls pairing big with a fixed disparity)
    lines through the origin (walls pairing c with big)
The depth-0 boundary should then be exactly big = 7c (the S <= 7 wall).  Test by bisection.
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
MID=[74,96,127,159,175]
print("  bisecting the depth-0 boundary in c, for each fixed 'big':\n")
print(f"  {'big':>8} {'c* (boundary)':>20} {'big/c*':>12} {'= 7 exactly?':>14}")
ok=True
for big in (215,218,221,224,227,230,240,260):
    L,H=F(20),F(60)
    while H-L>F(1,10**12):
        M=(L+H)/2
        ds=[M]+MID+[F(big)]
        d=depth(ds)
        if d is not None and d>0: L=M
        else: H=M
    r=F(big)/H
    exact = abs(float(r)-7)<1e-9
    ok &= exact
    print(f"  {big:>8} {float(H):>20.10f} {float(r):>12.9f} {str(exact):>14}")
print(f"\n  all boundaries satisfy big = 7c : {ok}")
print("  -> the depth-0 wall is the homogeneous line big = 7c, i.e. S = 7.  Not a box boundary.")
print()
print("  scale-invariance of the whole field (homogeneity), spot check:")
for k in (2,3,5):
    a=depth([F(30)]+MID+[F(224)])
    b=depth([F(30*k)]+[F(m*k) for m in MID]+[F(224*k)])
    print(f"    x{k}: depth {a} -> {b}   {'invariant' if a==b else 'CHANGED'}")
