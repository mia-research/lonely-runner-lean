"""v3: banded climb reached 27 vs unbanded 23 on equal budget, and the UNBANDED climb converged to
S = 7.51 on its own -- it found the band without being told.  Push the directed search against the
28 record, with a larger budget and a wider band sweep.  All speeds positive."""
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
def depth(ds):
    ds=[F(d) for d in ds]
    if min(ds)<=0 or len(set(ds))!=len(ds): return None
    t=TH/min(ds); n=0
    while n<40000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n
        t=max(nextOp(d,t) for d in b); n+=1
    return None
def climb(rng, lo, hi, restarts, steps, CMAX=90):
    best=(0,None)
    for _ in range(restarts):
        ds=None
        for _ in range(200):
            c=rng.randrange(20,CMAX)
            xs=sorted(rng.sample(range(c+1, int(hi*c)), 6))
            t=[c]+xs
            if len(set(t))==7 and lo < max(t)/min(t) < hi: ds=sorted(t); break
        if ds is None: continue
        cur=depth(ds) or 0; stall=0
        for _ in range(steps):
            w=list(ds); k=rng.randrange(7)
            w[k]+=rng.choice([-4,-3,-2,-1,1,2,3,4])
            if min(w)<=0 or len(set(w))!=7: continue
            w=sorted(w)
            if not (lo < max(w)/min(w) < hi): continue
            d=depth(w)
            if d is None: continue
            if d>cur: ds,cur,stall=w,d,0
            elif d==cur: ds,stall=w,stall+1
            else: stall+=1
            if stall>150: break
        if cur>best[0]: best=(cur,tuple(ds))
    return best
print(f"  {'band':>14} {'best depth':>11}   witness")
overall=(0,None,None)
for lo,hi in ((7.0,7.3),(7.3,7.6),(7.6,8.0),(8.0,8.6),(8.6,9.5)):
    b=climb(random.Random(int(lo*1000)), lo, hi, 150, 600)
    print(f"  ({lo:.1f},{hi:.1f}) {b[0]:>11}   {list(b[1]) if b[1] else None}")
    if b[0]>overall[0]: overall=(b[0],b[1],(lo,hi))
print(f"\n  BEST OVERALL: depth {overall[0]}  in band {overall[2]}")
if overall[1]:
    ds=list(overall[1]); print(f"    disparities {ds}   S = {max(ds)/min(ds):.4f}")
    print(f"    verify: depth recomputed = {depth(ds)}")
    print(f"    record on file was 28 -> {'BEATS IT' if overall[0]>28 else ('matches' if overall[0]==28 else 'below')}")
