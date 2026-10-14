"""The plateau boundaries are exact small-denominator rationals:
    18->23 at 1225/41,  23->19 at 1431/47,  19->18 at 518/17.
1225 = 175 x 7 with 175 a disparity and 7 = 8.1 - 1, and 41 = 8.5 + 1 -- the band-edge form
    c* = e(8M +- 1)/(8N + 1).
Confirm the mechanism: at each boundary, trace either side, find the first differing step, and
identify which disparity sits exactly on a band edge there.  All speeds positive."""
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
REST=[74,96,127,159,175,224]
def trace(c):
    ds=[F(c)]+[F(r) for r in REST]
    t=TH/min(ds); out=[]
    for _ in range(40000):
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return out
        tn,s=max((nextOp(d,t),d) for d in b)
        out.append((tuple(sorted(int(x) if x.denominator==1 else float(x) for x in b)), s, 1/(8*t)))
        t=tn
    return out
for cstar,lab in ((F(1225,41),"18 -> 23"), (F(1431,47),"23 -> 19"), (F(518,17),"19 -> 18")):
    eps=F(1,100000)
    lo=trace(cstar-eps); hi=trace(cstar+eps)
    k=0
    while k<min(len(lo),len(hi)) and lo[k][0]==hi[k][0] and lo[k][1]==hi[k][1]: k+=1
    print(f"  boundary {lab}  at c* = {cstar} = {float(cstar):.6f}   depths {len(lo)} / {len(hi)}")
    print(f"    trajectories agree for {k} steps, diverge at step {k}")
    if k<min(len(lo),len(hi)):
        print(f"      below: blockers {lo[k][0]}  setter {lo[k][1]}  scale {float(lo[k][2]):.6f}")
        print(f"      above: blockers {hi[k][0]}  setter {hi[k][1]}  scale {float(hi[k][2]):.6f}")
        D=lo[k][2]
        print(f"      readings at that scale (below): " +
              ", ".join(f"{float(F(r)/D):.4f}" for r in [int(cstar)]+REST))
    # the band-edge identity
    print(f"    band-edge check -- c* = e(8M+-1)/(8N+1) for some disparity e:")
    found=False
    for e in REST:
        num=cstar*F(1,e)          # = (8M+-1)/(8N+1)
        p,q=num.numerator,num.denominator
        if (q-1)%8==0 and (abs(p)%8 in (1,7)):
            Nn=(q-1)//8; Mm=(p+1)//8 if p%8==7 else (p-1)//8
            print(f"      e = {e}:  c*/e = {p}/{q},  8N+1 = {q} (N={Nn}),  {p} = 8*{(p+1)//8 if p%8==7 else (p-1)//8}{'-1' if p%8==7 else '+1'}   MATCH")
            found=True
    if not found: print(f"      no single-disparity match at this edge")
    print()
