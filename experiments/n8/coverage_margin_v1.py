"""Is there ANY uniform margin for a covering bound to beat?
Existence holds iff the bad set misses a point of (0, d_min].  A covering argument would need
   coverage <= 1 - c   for some c > 0 uniform over arrangements.
If inf(1 - coverage) = 0 -- i.e. coverage can be driven arbitrarily close to 1 -- then no uniform
covering bound exists, and the route is dead whatever the firewall says.
Adversarial: MINIMISE the clear measure.  Exact Fraction; M capped with the tail carried."""
import random, time
from fractions import Fraction as F
from math import gcd
MCAP=3000
def clear_measure(ds):
    m=min(ds); iv=[]
    for d in ds:
        d=F(d)
        for M in range(1,MCAP+1):
            lo=d/(8*M+1)
            if lo>=m: continue
            hi=min(d/(8*M-1), m)
            if hi>lo: iv.append((lo,hi))
    iv.sort(); tot=F(0); a=b=None
    for lo,hi in iv:
        if a is None: a,b=lo,hi
        elif lo<=b: b=max(b,hi)
        else: tot+=b-a; a,b=lo,hi
    if a is not None: tot+=b-a
    tail=sum(F(d)/(32*MCAP) for d in ds)          # upper bound on omitted bad measure
    clear_lo = 1 - float(tot/m) - float(tail/m)   # conservative: assume the tail is all bad
    return max(clear_lo,0.0), float(tot/m)

print(f"{'range':>12} {'best (smallest) clear fraction':>32} {'coverage':>10}  witness")
rng=random.Random(2026)
for HI in [20,40,80,160,320]:
    t0=time.time(); best=(1.0,None,0)
    while time.time()-t0<45:
        ds=sorted(rng.sample(range(1,HI),7))
        g=0
        for d in ds: g=gcd(g,d)
        if g!=1: continue
        c,cov=clear_measure(ds); cur=c
        for _ in range(150):
            if time.time()-t0>45: break
            cand=list(ds); i=rng.randrange(7)
            cand[i]=max(1,cand[i]+rng.choice([-3,-2,-1,1,2,3]))
            cand=sorted(set(cand))
            if len(cand)!=7: continue
            g=0
            for d in cand: g=gcd(g,d)
            if g!=1: continue
            c2,cov2=clear_measure(cand)
            if c2<=cur:
                ds,cur=cand,c2
                if c2<best[0]: best=(c2,tuple(ds),cov2)
    print(f"{'[1,'+str(HI)+')':>12} {best[0]:>32.8f} {best[2]:>10.6f}  {best[1]}")
