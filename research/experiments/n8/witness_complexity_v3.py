"""v2's hill-climb reached M = 13, refuting the M <= 7 impression from v1's random sample.
The search was weak, so: harder search, and test the obvious driver.

HYPOTHESIS to kill or keep: M is large when the WITNESS SET is thin -- when
   margin = max_t min_d ||d t||  is barely above 1/8.
Counter-datum already in hand: the AP has margin exactly 0 (max = 1/8 exactly) and M = 1.
So thinness cannot be the whole story.  Measure the correlation directly.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
import random
from collections import Counter
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def minM(ds,MCAP=200):
    for M in range(1,MCAP+1):
        N=8*M
        for lam in range(1,N):
            t=F(lam,N)
            if all(circd(F(d)*t)>=TH for d in ds): return M
    return None
def margin(ds,Q=2520):
    """max over t = a/Q of min_d ||d t||  -- a fine but finite probe of the true margin"""
    best=F(0)
    for a in range(1,Q):
        m=min(circd(F(d)*F(a,Q)) for d in ds)
        if m>best: best=m
    return best
def sds(v,i): return [F(abs(v[j]-v[i])) for j in range(8) if j!=i]

print("=== stronger adversarial search ===")
rng=random.Random(31337)
best=(0,None)
trace=Counter()
for restart in range(180):
    v=list(speeds(rng.sample(range(1,400),8)))
    cur=max((minM(sds(speeds(v),i)) or 0) for i in range(8))
    stall=0
    for step in range(500):
        w=list(v); k=rng.randrange(8)
        w[k]+=rng.choice([-8,-5,-3,-2,-1,1,2,3,5,8])
        if w[k]<1 or len(set(w))<8: continue
        try: wv=speeds(w)
        except Exception: continue
        val=max((minM(sds(wv,i)) or 0) for i in range(8))
        if val>cur: v,cur,stall=list(wv),val,0
        elif val==cur: v,stall=list(wv),stall+1
        else: stall+=1
        if stall>160: break
    trace[cur]+=1
    if cur>best[0]: best=(cur,tuple(v))
print(f"  largest minimal M found : {best[0]}   at {list(best[1])}")
print(f"  per-restart best M      : {dict(sorted(trace.items()))}")

print("\n=== is M driven by a thin margin? ===")
rng=random.Random(5)
rows=[]
for _ in range(120):
    v=speeds(rng.sample(range(1,120),8))
    for i in range(8):
        ds=sds(v,i); m=minM(ds)
        if m is None: continue
        rows.append((m,float(margin(ds))))
byM={}
for m,g in rows: byM.setdefault(m,[]).append(g)
print("   M   n     mean margin   min margin")
for m in sorted(byM):
    a=byM[m]
    print(f"  {m:>2}  {len(a):>4}    {sum(a)/len(a):.5f}      {min(a):.5f}")
print(f"\n  (threshold is 1/8 = 0.125; margin is max over t = a/2520 of min_d ||d t||)")
ap=speeds((1,2,3,4,5,6,7,8))
print(f"  AP {list(ap)} subject 1: M = {minM(sds(ap,0))}, margin = {float(margin(sds(ap,0))):.5f}")
