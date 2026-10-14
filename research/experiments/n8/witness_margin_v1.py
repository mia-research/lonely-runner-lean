"""The cascade's witness is TIGHT BY CONSTRUCTION: the final move sets t = (k+1/8)/d, putting the
setter at circle-distance exactly 1/8.  So the cascade always lands ON the threshold with zero
slack.  The multiplier search has no such constraint.

Quantify: the witness MARGIN (min over disparities of the circle distance) for each route.
Margin matters -- a witness with slack survives perturbation and rounding; one at exactly 1/8
does not.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
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
def cascade(ds):
    t=TH/min(ds); n=0
    while n<4000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return t,n
        t=max(nextOp(d,t) for d in b); n+=1
    return None,None
def best_mult(ds,MCAP=200):
    """first witness found by scanning M, and the best margin over that same M"""
    for M in range(1,MCAP+1):
        N=8*M; found=None
        for lam in range(1,N):
            tt=F(lam,N); m=min(circd(F(d)*tt) for d in ds)
            if m>=TH and (found is None or m>found[0]): found=(m,tt)
        if found: return found
    return None,None
rng=random.Random(606)
casc=[]; mult=[]; casc_tight=0; tot=0
for _ in range(500):
    v=speeds(rng.sample(range(1,90),8))
    for i in range(8):
        ds=[F(abs(v[j]-v[i])) for j in range(8) if j!=i]
        t,n=cascade(ds)
        if t is None: continue
        mc=min(circd(F(d)*t) for d in ds)
        mm,tt=best_mult(ds)
        if mm is None: continue
        tot+=1; casc.append(float(mc)); mult.append(float(mm))
        if mc==TH: casc_tight+=1
def st(x,name):
    x=sorted(x); n=len(x)
    print(f"  {name:<34} min {x[0]:.4f}  median {x[n//2]:.4f}  mean {sum(x)/n:.4f}  max {x[-1]:.4f}")
print(f"  {tot} subjects   (threshold = 1/8 = 0.1250)\n")
st(casc,"cascade witness margin")
st(mult,"multiplier witness margin")
print(f"\n  cascade lands EXACTLY on the threshold : {casc_tight}/{tot}  ({casc_tight/tot:.4f})")
print(f"  multiplier margin strictly greater     : {sum(1 for a,b in zip(casc,mult) if b>a)}/{tot}")
