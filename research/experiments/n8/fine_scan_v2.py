"""v1 CORRECTED the picture: depth is a STEP FUNCTION with wide plateaus, not a spike field.
At 0.1 resolution only four values appear -- {0,18,19,23} -- and depth 23 occupies [29.9, 30.4],
a plateau of width 0.6, not a knife-edge.  My "23 is a knife-edge" was an artifact of integer steps.

So find the exact boundaries and name the event at each.  Scan at 0.01 (baseline x100), bisect to
the exact rational, then identify which disparity/lap crossing flips there.
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
def run(c, REST):
    """depth and the setter/lap sequence, for minimum c (a Fraction) against REST"""
    ds=[F(c)]+[F(r) for r in REST]
    if min(ds)<=0 or len(set(ds))!=len(ds): return None,None
    t=TH/min(ds); n=0; seq=[]
    while n<40000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n,seq
        tn,s=max((nextOp(d,t),d) for d in b)
        seq.append((int(s) if s.denominator==1 else float(s), int(floor(s*t-TH))+1 if False else None))
        t=tn; n+=1
    return None,None
REST=[74,96,127,159,175,224]
def depth(c): return run(c,REST)[0]
print("  0.01-resolution scan of the minimum, 29.80 .. 30.60\n")
prev=None; edges=[]
for k in range(2980,3061):
    c=F(k,100); d=depth(c)
    if prev is not None and d!=prev[1]:
        edges.append((prev[0], c, prev[1], d))
    prev=(c,d)
for lo,hi,a,b in edges:
    print(f"    depth {a} -> {b}  between c = {float(lo):.2f} and {float(hi):.2f}")
print("\n  bisecting each edge to the exact rational boundary:")
for lo,hi,a,b in edges:
    L,H=lo,hi
    for _ in range(40):
        M=(L+H)/2
        if depth(M)==a: L=M
        else: H=M
    print(f"    depth {a} -> {b} at c* between {L} and {H}")
    print(f"       ~ {float(L):.6f}   ({L.limit_denominator(2000)} .. {H.limit_denominator(2000)})")
    # what is the reading profile at the boundary?
    print(f"       readings at c = {H.limit_denominator(2000)}: " +
          ", ".join(f"{float(F(r)/H):.4f}" for r in REST))
