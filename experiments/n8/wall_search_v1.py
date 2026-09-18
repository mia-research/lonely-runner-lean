"""Walls sit at c* = e(8M +- 1)/(8N + 1).  They are ENUMERABLE from the disparity set.  Two tests:

 (A) do enumerated walls reproduce the observed cell boundaries?
     (census found 159/7, 175/7, 175.7/41, 1431/47, 74.7/17, 224.9/65, 224/7 -- six of seven are
      of that form with e an original disparity; 1431/47 is not, so enumeration should find 6/7)

 (B) deep cells are narrow, and narrow cells live where walls CROWD.  So probe the tightest wall
     gaps and measure depth there, against probing random points in the same range.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from math import floor
import random, statistics as st
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
def walls(REST, lo, hi, MMAX=14, NMAX=14):
    W=set()
    for e in REST:
        for N in range(0,NMAX+1):
            q=8*N+1
            for M in range(0,MMAX+1):
                for p in (8*M+1, 8*M-1):
                    if p<=0: continue
                    c=F(e*p, q)
                    if lo<c<hi: W.add(c)
    return sorted(W)
REST=[74,96,127,159,175,224]
OBS=[F(159,7),F(175,7),F(1225,41),F(1431,47),F(518,17),F(2016,65),F(224,7)]
W=walls(REST,20,60)
print(f"(A) enumerated walls in [20,60]: {len(W)}")
hit=[w for w in OBS if w in W]
print(f"    observed cell boundaries recovered: {len(hit)}/{len(OBS)}   missing: {[str(w) for w in OBS if w not in W]}")

print(f"\n(B) probing the tightest wall gaps vs random points, c in [20,32]")
Wr=[w for w in W if 20<w<32]
gaps=sorted(((Wr[i+1]-Wr[i], Wr[i], Wr[i+1]) for i in range(len(Wr)-1)))
print(f"    {len(Wr)} walls, {len(gaps)} gaps;  tightest gap {float(gaps[0][0]):.6f}, widest {float(gaps[-1][0]):.6f}")
def probe(cands):
    out=[]
    for c in cands:
        d=depth([c]+REST)
        if d is not None: out.append(d)
    return out
tight=[ (a+b)/2 for _,a,b in gaps[:60] ]
wide =[ (a+b)/2 for _,a,b in gaps[-60:] ]
rng=random.Random(4242)
rand =[ F(rng.randrange(2000,3200),100) for _ in range(60) ]
for lab,c in (("tightest 60 gaps",tight),("widest 60 gaps",wide),("random 60 points",rand)):
    d=probe(c)
    print(f"    {lab:<18} n={len(d):>3}  mean depth {st.mean(d):>6.2f}  max {max(d):>3}  P(>=20) {sum(1 for x in d if x>=20)/len(d):.3f}")
