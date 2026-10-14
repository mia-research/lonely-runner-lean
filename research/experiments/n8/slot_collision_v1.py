"""Owner hypothesis (2026-09-18): the hard arrangements are those with two runners in the SAME
AP slot -- 'r5 and r6 are in the gap'.  Test: does slot occupancy predict R?
AP gap anchored slowest-to-fastest = W/7; slot(x) = round(x/gap).  Exact Fraction cascade."""
import random
from fractions import Fraction as F
from math import floor, ceil
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def inWay(d,t): return circd(d*t)<TH
def nextOp(d,t):
    k=ceil(d*t-TH)
    if k<0:k=0
    while F(k,1)+TH<d*t:k+=1
    return (F(k,1)+TH)/d
def R_of(ds,cap=3000):
    m=min(ds); t=TH/m; n=0
    while n<cap:
        b=[d for d in ds if inWay(d,t)]
        if not b: return float(8*m*t), n
        t=max(nextOp(d,t) for d in b); n+=1
    return None,n
def slots(v):
    """v = full arrangement (8 values, subject at 0). gap = W/7. returns slot list."""
    W=max(v); gap=W/7
    return [int((x/gap)+F(1,2)) for x in v]        # round-half-up, exact
def profile(v):
    s=slots(v); occ={}
    for k in s: occ[k]=occ.get(k,0)+1
    dup=sum(c-1 for c in occ.values() if c>1)      # excess occupancy
    holes=sum(1 for k in range(8) if occ.get(k,0)==0)
    return dup,holes,s

print("the extremal arrangement found by five independent searches")
ex=[F(0),F(1),F(2365,1000),F(3231,1000),F(4173,1000),F(5231,1000),F(5827,1000),F(7462,1000)]
d,h,s=profile(ex)
print(f"   arrangement {[round(float(x),3) for x in ex]}")
print(f"   AP gap W/7 = {float(max(ex)/7):.4f}")
print(f"   slots      {s}      duplicated: {d}   empty slots: {h}")
print()

print("does slot collision predict R?  random integer arrangements, exact")
rng=random.Random(5)
buckets={}
for _ in range(9000):
    v=sorted(rng.sample(range(0,80),8))
    v=[F(x-v[0]) for x in v]
    for i in range(8):
        ds=sorted(abs(v[j]-v[i]) for j in range(8) if j!=i)
        R,n=R_of(ds)
        if R is None: continue
        dup,holes,_=profile(sorted(abs(x-v[i]) for x in v))   # subject-centred, includes 0
        buckets.setdefault(dup,[]).append((R,n))
print(f"   {'dup slots':>10} {'n':>8} {'max R':>10} {'mean R':>9} {'frac R>2':>9} {'max moves':>10}")
for k in sorted(buckets):
    b=buckets[k]; Rs=[r for r,_ in b]
    print(f"   {k:>10} {len(b):>8} {max(Rs):>10.4f} {sum(Rs)/len(Rs):>9.4f} "
          f"{sum(1 for r in Rs if r>2)/len(Rs):>9.3f} {max(n for _,n in b):>10}")
