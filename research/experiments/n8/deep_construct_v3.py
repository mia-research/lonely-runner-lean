"""v2 refuted the Sigma lever: maximising Sigma (all disparities clustered high) gave depth 2,
because clustered disparities block SIMULTANEOUSLY -- maximum overlap, so crossings collapse into
few steps.  Random in-band beat both structured strategies.

So the real insight is the BAND (S just above 7), not Sigma.  Use it to DIRECT the search rather
than replace it: hill-climb with S constrained to (7, 8), versus an unconstrained climb with the
same budget.  If the constraint finds deeper cases per unit compute, the band insight is doing work.
All speeds positive."""
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
def climb(rng, banded, restarts, steps, HI=400):
    best=(0,None)
    for _ in range(restarts):
        while True:
            c=rng.randrange(20,HI//7)
            xs=sorted(rng.sample(range(c+1, int(7.9*c) if banded else HI), 6))
            ds=[c]+xs
            if len(set(ds))==7 and (not banded or 7 < max(ds)/min(ds) < 8): break
        cur=depth(ds) or 0
        stall=0
        for _ in range(steps):
            w=list(ds); k=rng.randrange(7)
            w[k]+=rng.choice([-5,-3,-2,-1,1,2,3,5])
            if min(w)<=0 or len(set(w))!=7: continue
            w=sorted(w)
            if banded and not (7 < max(w)/min(w) < 8): continue
            d=depth(w)
            if d is None: continue
            if d>cur: ds,cur,stall=w,d,0
            elif d==cur: ds,stall=w,stall+1
            else: stall+=1
            if stall>120: break
        if cur>best[0]: best=(cur,tuple(sorted(ds)))
    return best
rng=random.Random(777)
bb=climb(random.Random(11), True,  120, 400)
ub=climb(random.Random(11), False, 120, 400)
print(f"  BANDED   climb (S constrained to (7,8)) : best depth {bb[0]:>3}   {list(bb[1])}")
if bb[1]: print(f"     S = {max(bb[1])/min(bb[1]):.4f}")
print(f"  UNBANDED climb (same budget)            : best depth {ub[0]:>3}   {list(ub[1])}")
if ub[1]: print(f"     S = {max(ub[1])/min(ub[1]):.4f}")
print(f"\n  adversarial record on file: 23 and 28")
for lab,r in (("banded",bb),("unbanded",ub)):
    v = "BEATS 28" if r[0]>28 else ("beats 23" if r[0]>23 else "below 23")
    print(f"    {lab:<9} {r[0]:>3}  -> {v}")
