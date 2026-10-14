"""Two tests.

(A) The parallel session's relay claim: deep cascades need ALL SEVEN disparities participating as
    setters.  Testable -- count distinct setters against depth.

(B) Search PROFILE space directly (6 continuous parameters) rather than integer space.  Different
    search space; may find families the integer climbs cannot reach.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor
import random, statistics as st
from collections import Counter
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
    t=TH/min(ds); n=0; seq=[]
    while n<200000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n,seq
        t,s=max((nextOp(d,t),d) for d in b); seq.append(s); n+=1
    return None,None
def depth(ds): return run(ds)[0]

print("(A) distinct setters vs depth")
rng=random.Random(606); tab={}
for _ in range(4000):
    v=speeds(rng.sample(range(1,90),8))
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        n,seq=run(ds)
        if n is None or n==0: continue
        k=len(set(seq))
        tab.setdefault(n if n<12 else 12,[]).append(k)
print(f"    {'depth':>6} {'n':>6} {'mean distinct setters':>23} {'max':>5}")
for d in sorted(tab):
    a=tab[d]
    if len(a)<15: continue
    lab=f"{d}" if d<12 else ">=12"
    print(f"    {lab:>6} {len(a):>6} {st.mean(a):>23.3f} {max(a):>5}")
for name,ds in (("23-move",[30,74,96,127,159,175,224]),("28-move",[49,205,234,256,286,323,366])):
    n,seq=run(ds); print(f"    {name}: depth {n}, distinct setters {len(set(seq))} of 7")

print("\n(B) direct search in PROFILE space (6 continuous parameters, c = 2000)")
C=2000
def inst(r):
    ds=sorted({int(round(C*x)) for x in r})
    return ds if len(ds)==7 else None
def dep_r(r):
    ds=inst(r)
    return depth(ds) if ds else None
rng=random.Random(20260918)
best=(0,None)
found=[]
for restart in range(300):
    r=[1.0]+sorted(rng.uniform(1.05,7.9) for _ in range(6))
    r[6]=rng.uniform(7.05,7.95)
    r=[1.0]+sorted(r[1:])
    cur=dep_r(r) or 0; stall=0
    for _ in range(1200):
        w=list(r); k=rng.randrange(1,7)
        w[k]+= rng.gauss(0,0.05)
        w=[1.0]+sorted(w[1:])
        if w[1]<=1.02 or w[6]>7.97 or any(w[i+1]-w[i]<0.03 for i in range(6)): continue
        d=dep_r(w)
        if d is None: continue
        if d>cur: r,cur,stall=w,d,0
        elif d==cur: r,stall=w,stall+1
        else: stall+=1
        if stall>300: break
    if cur>=22: found.append((cur,tuple(round(x,3) for x in r)))
    if cur>best[0]: best=(cur,tuple(round(x,3) for x in r))
found.sort(reverse=True)
print(f"    {len(found)} profiles with depth >= 22 from 300 restarts")
for d,r in found[:10]:
    print(f"      depth {d:>3}: " + " ".join(f"{x:>6.3f}" for x in r))
print(f"\n    BEST: depth {best[0]}   {list(best[1]) if best[1] else None}")
print(f"    record is 28 -> {'BEATS IT' if best[0]>28 else ('matches' if best[0]==28 else 'below')}")
