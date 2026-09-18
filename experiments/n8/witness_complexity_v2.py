"""v1 found minimal M <= 7 over 3200 random subjects.  That is a positive, so TEST it rather than
report it -- random sampling is exactly where a bound looks good and a hard case breaks it.

Three attacks:
  1. the hard arrangements already on file (high R / thin margin)
  2. wider speed ranges -- does M grow with the speeds?
  3. an adversarial hill-climb that maximises minimal M directly
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
from collections import Counter
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def minM(ds,MCAP=3000):
    for M in range(1,MCAP+1):
        N=8*M
        for lam in range(1,N):
            if gcd(lam,N)!=1 and M>1: pass
            t=F(lam,N)
            if all(circd(F(d)*t)>=TH for d in ds): return M
    return None
def subj_ds(v,i): return [F(abs(v[j]-v[i])) for j in range(8) if j!=i]

print("=== 1. hard arrangements on file ===")
hard=[(27,70,133,190,243,297,340,393),
      (1,31,75,97,128,160,176,225),
      (11,21,22,23,26,34,35,40),
      (1,2,3,4,5,6,7,8),
      (2,3,4,5,6,7,16,23)]
for v in hard:
    v=speeds(v)
    Ms=[minM(subj_ds(v,i)) for i in range(8)]
    print(f"    {str(list(v)):<40} minimal M per subject: {Ms}   max {max(Ms)}")

print("\n=== 2. does M grow with the speed range? ===")
for HI in (20,50,100,300,1000,5000):
    rng=random.Random(11); worst=0; tot=0; acc=Counter()
    for _ in range(60):
        v=speeds(rng.sample(range(1,HI+1),8))
        for i in range(8):
            m=minM(subj_ds(v,i))
            if m is None: continue
            acc[m]+=1; tot+=1; worst=max(worst,m)
    print(f"    speeds 1..{HI:<5} n={tot:<4} max minimal M = {worst:<4} distribution {dict(sorted(acc.items())[:8])}")

print("\n=== 3. adversarial hill-climb: maximise minimal M ===")
rng=random.Random(777)
best=(0,None,None)
for restart in range(60):
    v=list(speeds(rng.sample(range(1,200),8)))
    cur=max((minM(subj_ds(speeds(v),i)) or 0) for i in range(8))
    for step in range(220):
        w=list(v); k=rng.randrange(8)
        w[k]=w[k]+rng.choice([-3,-2,-1,1,2,3])
        if w[k]<1 or len(set(w))<8: continue
        try: wv=speeds(w)
        except Exception: continue
        val=max((minM(subj_ds(wv,i)) or 0) for i in range(8))
        if val>=cur: v, cur = list(wv), val
    if cur>best[0]: best=(cur,tuple(v),None)
print(f"    largest minimal M found: {best[0]}   at {list(best[1]) if best[1] else None}")
