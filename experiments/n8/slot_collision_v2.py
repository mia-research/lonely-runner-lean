"""v2 -- ARRANGEMENTS, not difference sets.  v1 reconstructed an arrangement from a disparity set
by putting the subject at 0 (a stationary runner, sec 6A) and all others above it: one of up to 128
sign patterns, and a pinned frame.  Here: eight distinct POSITIVE speeds, no zero, every subject
read in place.  Slots are the arrangement's own, gap = (v_max - v_min)/7.  Exact Fraction."""
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
def R_of(ds,cap=4000):
    m=min(ds); t=TH/m; n=0
    while n<cap:
        b=[d for d in ds if inWay(d,t)]
        if not b: return float(8*m*t), n
        t=max(nextOp(d,t) for d in b); n+=1
    return None,n
def dup_of(v):
    lo=min(v); gap=(max(v)-lo)/7
    occ={}
    for x in v:
        k=int(((x-lo)/gap)+F(1,2)); occ[k]=occ.get(k,0)+1
    return sum(c-1 for c in occ.values() if c>1)

print("the extremal arrangement, stated with NO zero speed (subject = 1):")
ex=[F(1),F(2),F(3365,1000),F(4231,1000),F(5173,1000),F(6231,1000),F(6827,1000),F(8462,1000)]
print("   speeds", [round(float(x),3) for x in ex])
print("   spread W =", round(float(max(ex)-min(ex)),4), " AP gap W/7 =", round(float((max(ex)-min(ex))/7),4))
lo=min(ex); gap=(max(ex)-lo)/7
print("   slots ", [int(((x-lo)/gap)+F(1,2)) for x in ex], "  duplicated:", dup_of(ex))
print()
print("arrangement-level: 8 distinct positive speeds, hard band S in [7,8] per subject")
rng=random.Random(404); D=1000
buckets={}
for _ in range(30000):
    v=sorted({F(rng.randint(D,9*D),D) for _ in range(8)})
    if len(v)!=8: continue
    d=dup_of(v)
    for i in range(8):
        ds=sorted(abs(v[j]-v[i]) for j in range(8) if j!=i)
        S=max(ds)/min(ds)
        if not (7<=S<=8): continue
        R,n=R_of(ds)
        if R is None: continue
        buckets.setdefault(d,[]).append((R,n))
print(f"   {'dup slots':>10} {'n':>8} {'max R':>10} {'mean R':>9} {'frac R>3':>9} {'max moves':>10}")
for k in sorted(buckets):
    b=buckets[k]; Rs=[r for r,_ in b]
    print(f"   {k:>10} {len(b):>8} {max(Rs):>10.4f} {sum(Rs)/len(Rs):>9.4f} "
          f"{sum(1 for r in Rs if r>3)/len(Rs):>9.4f} {max(n for _,n in b):>10}")
