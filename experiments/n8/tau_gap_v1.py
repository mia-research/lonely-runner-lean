"""tau = d_min . t* = R/8.  Random subjects: max tau = 0.503 over 28,387.  All four deep cases:
tau in [1.28, 1.36].  Is there a GAP in tau between ~0.5 and ~1.28, or does it fill in?

Harvest cascades across the whole depth range (banded search reaches deep ones) and plot tau
against depth.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor
import random, statistics as st
from collections import defaultdict
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def run(ds):
    ds=[F(d) for d in ds]
    if min(ds)<=0 or len(set(ds))!=len(ds): return None,None
    t=TH/min(ds); n=0
    while n<200000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n, float(F(min(ds))*t)
        t=max(nextOp(d,t) for d in b); n+=1
    return None,None
rng=random.Random(2026)
bydepth=defaultdict(list)
for _ in range(20000):
    v=speeds(rng.sample(range(1,120),8))
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        n,tau=run(ds)
        if n is not None: bydepth[n].append(tau)
# add banded-search deep cases
for _ in range(120000):
    c=rng.randrange(20,70); xs=sorted(rng.sample(range(c+1,int(7.95*c)),6)); ds=[c]+xs
    if len(set(ds))!=7 or not (7<max(ds)/min(ds)<8): continue
    n,tau=run(ds)
    if n is not None and n>=8: bydepth[n].append(tau)
print(f"  {'depth':>6} {'n':>7} {'min tau':>10} {'mean tau':>10} {'max tau':>10}")
for d in sorted(bydepth):
    a=bydepth[d]
    if len(a)<3 and d<15: continue
    print(f"  {d:>6} {len(a):>7} {min(a):>10.4f} {st.mean(a):>10.4f} {max(a):>10.4f}")
alltau=[x for a in bydepth.values() for x in a]
print(f"\n  overall: {len(alltau)} cascades, tau range [{min(alltau):.4f}, {max(alltau):.4f}]")
print(f"  tau >= 1 : {sum(1 for x in alltau if x>=1)}  ({sum(1 for x in alltau if x>=1)/len(alltau):.5f})")
# is there a gap?
s=sorted(alltau)
gaps=sorted(((s[i+1]-s[i], s[i], s[i+1]) for i in range(len(s)-1)), reverse=True)[:5]
print(f"  largest gaps in the observed tau values:")
for g,a,b in gaps: print(f"    gap {g:.4f} between {a:.4f} and {b:.4f}")
