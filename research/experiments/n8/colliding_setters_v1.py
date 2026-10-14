"""Next area: the COLLIDING subjects -- the 50.3% who fail every grid instant and must cascade.
This is sec 2.3's open item, and the only region where "which runners achieve the isolation" is
still unanswered.

Lead, surfaced in colliding_blocking_v1 and not followed: colliding disparities (8 | d/g) BLOCK
twice as often as non-colliding ones (31.0% vs 15.1%).  But their own 23-step trace shows colliding
disparities setting 7 of 23 steps while being 2 of 7 disparities -- 30.4% vs 28.6%, roughly
PROPORTIONAL.  Those two can both be true and mean different things.

Separate them properly:
  (a) P(a disparity ever blocks | colliding)      -- binary, per disparity
  (b) share of SETTER events                      -- who actually drives the cascade
  (c) share of the FINAL setter                   -- who lands the isolation
(c) is the one that answers "which runners achieve the isolation".
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def run(ds):
    t=TH/min(ds); n=0; setters=[]; blocked=set()
    while n<4000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return t,n,setters,blocked
        blocked|=set(b)
        t,s=max((nextOp(d,t),d) for d in b); setters.append(s); n+=1
    return None,None,None,None
rng=random.Random(1234)
ever_c=ever_cn=0; ever_n=ever_nn=0
set_c=set_tot=0; fin_c=fin_tot=0
nd_c=nd_tot=0
for _ in range(2500):
    v=speeds(rng.sample(range(1,90),8))
    g=gcd_all(v)
    for i in range(8):
        ds=[F(abs(v[j]-v[i])) for j in range(8) if j!=i]
        col={d for d in ds if (int(d)//g)%8==0}
        if not col: continue                      # COLLIDING SUBJECTS ONLY
        t,n,setters,blocked=run(ds)
        if t is None or n==0: continue
        for d in ds:
            if d in col:
                ever_cn+=1; ever_c += 1 if d in blocked else 0
            else:
                ever_nn+=1; ever_n += 1 if d in blocked else 0
        set_c+=sum(1 for s in setters if s in col); set_tot+=len(setters)
        fin_c+= 1 if setters[-1] in col else 0; fin_tot+=1
        nd_c+=len(col); nd_tot+=7
print(f"  colliding subjects with depth >= 1: {fin_tot}\n")
base=nd_c/nd_tot
print(f"  baseline: colliding share of disparities     {base:.4f}")
print(f"  (a) P(ever blocks | colliding)               {ever_c/ever_cn:.4f}")
print(f"      P(ever blocks | non-colliding)           {ever_n/ever_nn:.4f}")
print(f"  (b) colliding share of SETTER events         {set_c/set_tot:.4f}   (baseline {base:.4f})")
print(f"  (c) colliding share of the FINAL setter      {fin_c/fin_tot:.4f}   (baseline {base:.4f})")
print()
print("  (b) and (c) against the baseline are the real test: above it means colliding disparities")
print("  DRIVE the cascade; at it means they are simply present in proportion.")
