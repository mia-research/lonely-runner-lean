"""The open question is now concrete: is BAND 2 reachable?  R in [17,23] means d_min completes two
full laps before isolation.  Band 0 has 148,892 random cascades, band 1 all five deep cases, band 2
none.  Hunt for it directly by maximising R.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from math import floor
import random
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def Rof(ds):
    ds=[F(d) for d in ds]
    if min(ds)<=0 or len(set(ds))!=len(ds): return 0.0,None
    c=min(ds); t=TH/c; n=0
    while n<200000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return float(c*8*t), n
        t=max(nextOp(d,t) for d in b); n+=1
    return 0.0,None
best=(0,None,None)
rng=random.Random(987654)
for restart in range(500):
    # seed across a wide range of shapes, including near the known band-1 cases
    mode=restart%3
    c=rng.randrange(20,90)
    if mode==0: xs=sorted(rng.sample(range(c+1,int(7.95*c)),6))
    elif mode==1: xs=sorted(rng.sample(range(c+1,int(16*c)),6))
    else: xs=sorted(rng.sample(range(int(3*c),int(8*c)),6))
    ds=sorted(set([c]+xs))
    if len(ds)!=7: continue
    cur,_=Rof(ds); stall=0
    for _ in range(4000):
        w=list(ds); k=rng.randrange(7)
        w[k]+=rng.choice([-5,-3,-2,-1,1,2,3,5])
        if min(w)<=0 or len(set(w))!=7: continue
        w=sorted(w); val,_=Rof(w)
        if val>cur: ds,cur,stall=w,val,0
        elif val==cur: ds,stall=w,stall+1
        else: stall+=1
        if stall>600: break
    if cur>best[0]: best=(cur,tuple(ds),None)
R,ds,_=best
d=Rof(list(ds))[1]
print(f"  500 restarts x 4000 steps, three seeding modes")
print(f"  max R found : {R:.6f}   band {int(R//8)}")
print(f"    {list(ds)}   depth {d}   S = {max(ds)/min(ds):.4f}")
print(f"  band 2 needs R >= 17 -> {'REACHED' if R>=17 else 'NOT reached'}")
print(f"  previous best R was 11.618557; this search {'improved it' if R>11.618557 else 'did not improve it'}")
