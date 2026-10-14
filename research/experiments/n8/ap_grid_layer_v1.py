"""Owner, 2026-09-18: "for the scale determination we have AP and GRID to find anything that isn't
just AP at a different scale.  Is that your read?"   Tested as a coverage question, per subject.

L1  GRID / residue layer  -- an INTEGER scale dividing every disparity.  The best such scale is
    g = gcd(ds) (larger D only shrinks the readings), so the whole layer reduces to ONE test:
    no d/g is a multiple of 8.  Then Thm 4.10 makes the subject lonely at EVERY spine instant of
    scale g -- this is sec 4.5(a)-(c), AP and grid together.
L2  the k = 0 flank layer -- some disparity e, taken as the scale, with the band condition.
    Thm 4.8 is the case e = d_min.  Non-integer readings allowed.
L3  needs k >= 1, i.e. a NON-INTEGER scale e/(8k+1).
Exact Fraction."""
import random
from fractions import Fraction as F
from math import floor, gcd
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def lonely_at_scale(ds,D):
    t=F(1)/(8*D)
    return all(circd(F(d)*t)>=TH for d in ds)
def min_k(ds,KMAX=60):
    for k in range(KMAX+1):
        kk=F(k)+TH
        for e in ds:
            t=kk/F(e)
            if all(circd(F(d)*t)>=TH for d in ds): return k,e
    return None,None

for (LO,HI,label) in [(0,20,"speeds in [0,20)"),(0,60,"speeds in [0,60)"),(0,200,"speeds in [0,200)")]:
    rng=random.Random(31)
    n=0; L1=0; L2=0; L3={}
    for _ in range(4000):
        v=sorted(rng.sample(range(LO,HI),8))
        for i in range(8):
            ds=sorted(abs(v[j]-v[i]) for j in range(8) if j!=i)
            g=0
            for d in ds: g=gcd(g,d)
            n+=1
            l1 = all((d//g)%8!=0 for d in ds)          # grid/residue layer, scale g
            if l1: L1+=1
            l2 = any(lonely_at_scale(ds,F(e)) for e in ds)   # k=0 flank layer
            if l2: L2+=1
            if not l2:
                k,e=min_k(ds)
                L3[k]=L3.get(k,0)+1
    print(f"\n=== {label}   {n} runner-instances ===")
    print(f"   L1  GRID/residue layer (integer scale g, Thm 4.10) : {L1/n:.4f}")
    print(f"   L2  k = 0 flank layer (scale = a disparity)        : {L2/n:.4f}")
    print(f"   L3  needs k >= 1, scale e/(8k+1) NON-INTEGER       : {1-L2/n:.4f}")
    if L3:
        tot=sum(L3.values())
        print(f"       of those, minimal k: {dict(sorted(L3.items()))}   (max {max(L3)})")
