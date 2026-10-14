"""Three unasked questions.
Q1  Is "largest next opening" NECESSARY?  Compare alternative selection rules.
Q4  What is the SECOND lonely instant?  Thm 6.2(b) characterises the first; the lonely set is a
    union of intervals and its structure past the first has never been looked at.
Q5  The SEVEN-AT-THRESHOLD configurations: fixed points where many runners sit at exactly 1/8.
Exact Fraction."""
import random
from fractions import Fraction as F
from math import floor
from collections import Counter
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def blockers(ds,t): return [d for d in ds if circd(d*t)<TH]
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def run(ds,rule,cap=4000):
    m=min(ds); t=TH/m; n=0
    while n<cap:
        b=blockers(ds,t)
        if not b: return t,n
        if   rule=='max':  t=max(nextOp(d,t) for d in b)
        elif rule=='min':  t=min(nextOp(d,t) for d in b)
        elif rule=='big':  t=nextOp(max(b),t)
        elif rule=='small':t=nextOp(min(b),t)
        n+=1
    return None,cap

print("=== Q1: is 'largest next opening' necessary? ===")
rng=random.Random(12); stats={r:{'term':0,'same':0,'later':0,'steps':0} for r in ['max','min','big','small']}
tot=0
for _ in range(1200):
    v=sorted(rng.sample(range(0,70),8))
    for i in range(8):
        ds=sorted(F(abs(v[j]-v[i])) for j in range(8) if j!=i)
        t0,n0=run(ds,'max')
        if t0 is None: continue
        tot+=1
        for r in ['max','min','big','small']:
            t,n=run(ds,r)
            if t is None: continue
            stats[r]['term']+=1; stats[r]['steps']+=n
            if t==t0: stats[r]['same']+=1
            elif t>t0: stats[r]['later']+=1
print(f"   {tot} runner-instances where the cascade terminates")
print(f"   {'rule':>7} {'terminates':>11} {'same instant':>13} {'later':>7} {'mean steps':>11}")
for r in ['max','min','big','small']:
    s=stats[r]
    print(f"   {r:>7} {s['term']/tot:>11.4f} {s['same']/max(s['term'],1):>13.4f} {s['later']/max(s['term'],1):>7.4f} {s['steps']/max(s['term'],1):>11.2f}")

print()
print("=== Q4: the lonely set past the first instant ===")
def interval_end(ds,t):
    """first time after t at which some runner ENTERS a zone: (N - 1/8)/d"""
    best=None
    for d in ds:
        N=floor(d*t+TH)+1
        while (F(N)-TH)/d<=t: N+=1
        e=(F(N)-TH)/d
        if best is None or e<best: best=e
    return best
def next_lonely(ds,t,cap=3000):
    s=interval_end(ds,t); n=0
    while n<cap:
        b=blockers(ds,s)
        if not b: return s
        s=max(nextOp(d,s) for d in b); n+=1
    return None
rng=random.Random(3); w1=[]; gap=[]; ratio=[]
for _ in range(900):
    v=sorted(rng.sample(range(0,70),8))
    for i in range(8):
        ds=sorted(F(abs(v[j]-v[i])) for j in range(8) if j!=i)
        t1,_=run(ds,'max')
        if t1 is None: continue
        e1=interval_end(ds,t1); t2=next_lonely(ds,t1)
        if t2 is None: continue
        w1.append(float(e1-t1)); gap.append(float(t2-e1)); ratio.append(float(t2/t1))
import statistics as st
print(f"   first lonely interval width : mean {st.mean(w1):.6f}  median {st.median(w1):.6f}")
print(f"   gap to the next lonely set  : mean {st.mean(gap):.6f}  median {st.median(gap):.6f}")
print(f"   t2 / t1                     : mean {st.mean(ratio):.4f}  median {st.median(ratio):.4f}  max {max(ratio):.3f}")
print(f"   fraction with t2/t1 < 2     : {sum(1 for r in ratio if r<2)/len(ratio):.4f}")

print()
print("=== Q5: how many runners sit at EXACTLY 1/8 at the fixed point? ===")
rng=random.Random(77); best=(0,None,None); hist=Counter()
for _ in range(4000):
    v=sorted(rng.sample(range(0,60),8))
    for i in range(8):
        ds=sorted(F(abs(v[j]-v[i])) for j in range(8) if j!=i)
        t,n=run(ds,'max')
        if t is None: continue
        c=sum(1 for d in ds if circd(d*t)==TH)
        hist[c]+=1
        if c>best[0]: best=(c,[int(d) for d in ds],t)
print(f"   distribution: {dict(sorted(hist.items()))}")
print(f"   maximum {best[0]} of 7 at exactly 1/8")
print(f"     disparities {best[1]}   instant t = {best[2]}")
if best[1]:
    print(f"     positions d*t mod 1: {[str(F(d)*best[2]-floor(F(d)*best[2])) for d in best[1]]}")
