# What does error/M actually decay with?  sum(ds)?  min(ds)?  b?  Get the exponent, and check
# whether the relevant variable is the SUM or something else.  Exhaustive where feasible.
from math import gcd, log
from itertools import combinations
import random, statistics
def win(a,b):
    s=a%8; lo=-(-(b-s)//8); hi=(7*b-s)//8
    return hi-lo+1
def exact_main(ds):
    t=0.0
    for b in ds:
        x=float(b)
        for a in ds:
            if a!=b: x *= win(a,b)/b
        t+=x
    return t
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def T(ds): return sum(sum(1 for k in range(b) if all(clear(a,b,k) for a in ds)) for b in ds)
# bucket by sum(ds) and report the WORST error/M in each bucket (worst case is what matters)
buck={}
rng=random.Random(7)
for _ in range(60000):
    V=rng.choice([12,16,20,28,40,60,90,140,220,350])
    ds=sorted(rng.sample(range(1,V),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
    S=sum(ds); M=exact_main(ds); e=(M-T(ds))/M
    key=int(log(S)/log(2)*2)//1      # half-octave buckets in sum(ds)
    b=buck.setdefault(key,[])
    b.append((e,S,ds))
print(f"{'sum(ds) range':>18} {'n':>6} {'worst err/M':>12} {'median':>9}  worst set")
rows=[]
for key in sorted(buck):
    v=buck[key]; v.sort(key=lambda x:-x[0])
    Ss=[x[1] for x in v]
    if len(v)<40: continue
    w=v[0]
    rows.append((statistics.median(Ss), w[0]))
    print(f"{min(Ss):>8}-{max(Ss):<9} {len(v):>6} {w[0]:>12.4f} {statistics.median([x[0] for x in v]):>9.4f}  {w[2]}")
print()
# fit worst err/M ~ C * S^(-alpha)
import math
xs=[math.log(s) for s,_ in rows if _>0]; ys=[math.log(e) for _,e in rows if e>0]
n=len(xs); mx=sum(xs)/n; my=sum(ys)/n
alpha=-sum((x-mx)*(y-my) for x,y in zip(xs,ys))/sum((x-mx)**2 for x in xs)
C=math.exp(my+alpha*mx)
print(f"fit of the WORST error/M against sum(ds):   err/M ~ {C:.3f} * S^(-{alpha:.3f})")
print(f"  predicted worst err/M at S=28 (the minimum): {C*28**(-alpha):.3f}")
print(f"  requirement is err/M < 1 - 1/M, and M >= 5.24, so < 0.809")
print(f"  crossover S where the fit meets 0.809: S = {(C/0.809)**(1/alpha):.1f}")
