"""Item 1: the k=1 rung -- and the conjecture that clear_iff was never about d_min.

A cascade scale is D = e.g/(8N+1).  The reading of disparity a.g there is a(8N+1)/e, and clear
means no reading within 1 of a multiple of 8.  By the same algebra as clear_iff:

    CLEAR AT SCALE e/(8N+1)   <=>   for every disparity a:  e <= a(8N+1) mod 8e <= 7e

clear_iff is the case e = c (= d_min), N = 0.  If this holds, the cascade is a SEQUENCE of
applications of one residue-band test, with the host e and multiplier (8N+1) updating -- and the
k-th rung of the depth stratification is that test at the k-th scale.

Verified against the cascade at EVERY scale it visits, not just the first.  All speeds positive."""
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
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
rng=random.Random(2468)
agree=tot=0; rung=Counter(); depth_hit=Counter()
for _ in range(3000):
    v=speeds(rng.sample(range(1,90),8))
    g=gcd_all(v)
    for i in range(8):
        dsr=sorted(abs(v[j]-v[i])//g for j in range(8) if j!=i)     # reduced integers
        ds=[F(a*g) for a in dsr]
        # walk the cascade, carrying (e, N) for each scale
        e=min(dsr); N=0
        t=TH/min(ds); n=0
        while n<4000:
            # ground truth at this scale
            truth=all(circd(d*t)>=TH for d in ds)
            # criterion at this scale, using (e, N)
            crit=all(e <= (a*(8*N+1)) % (8*e) <= 7*e for a in dsr)
            tot+=1; agree += (truth==crit)
            if truth: rung[n]+=1; depth_hit[n]+=1; break
            b=[d for d in ds if circd(d*t)<TH]
            t,setter=max((nextOp(d,t),d) for d in b)
            e=int(setter)//g; N=int(setter*t-TH)
            n+=1
print(f"  scales tested (every scale the cascade visits): {tot}")
print(f"  CRITERION agrees with the cascade at that scale: {agree}/{tot}  ({agree/tot:.6f})\n")
print(f"  depth at which clearance first occurs: {dict(sorted(depth_hit.items())[:8])}")
c=0; s=sum(depth_hit.values())
for k in sorted(depth_hit):
    c+=depth_hit[k]
    if k<=4: print(f"    cumulative through rung k={k}: {c/s:.4f}")
print()
print("  criterion:  clear at scale e/(8N+1)  <=>  for every disparity a,  e <= a(8N+1) mod 8e <= 7e")
print("  clear_iff is the case e = d_min/g, N = 0.")
