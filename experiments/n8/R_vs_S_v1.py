"""Max R = 8*d_min*t as a function of the ratio cap S = d_max/d_min.
Thm 4.8 gives R = 1 for S <= 7.  The record R ~ 11.96 sits at S ~ 7.44.
The k=369 witness has S ~ 14,125 and R ~ 1.0.  So: does R PEAK just above 7 and decay?
If max R is bounded, a bounded-S certificate plus a large-S argument closes Existence.
Exact Fraction, adversarial hill-climb per band.  2026-09-18."""
import random, time
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
def Sof(ds): return float(max(ds)/min(ds))

rng=random.Random(918)
def rand_ds(Scap,dens):
    out={F(1)}
    while len(out)<7:
        out.add(F(rng.randint(dens, int(Scap*dens)),dens))
    ds=sorted(out)
    return ds if Sof(ds)<=Scap else None
def perturb(ds,Scap,dens):
    o=list(ds); i=rng.randrange(7)
    o[i]=o[i]+F(rng.choice([-5,-3,-2,-1,1,2,3,5]),dens)
    if o[i]<=0: return None
    o=sorted(set(o))
    if len(o)!=7 or Sof(o)>Scap: return None
    return o

print(f"{'S cap':>8} {'restarts':>9} {'max R':>10} {'S at max':>10} {'moves':>7}")
for Scap in [7.5,8,9,10,12,15,20,30,50,100,300,1000]:
    t0=time.time(); best=(0,None,0); r=0
    while time.time()-t0<50:
        r+=1
        dens=rng.choice([10,50,100,1000])
        ds=rand_ds(Scap,dens)
        if ds is None: continue
        R,n=R_of(ds)
        if R is None: continue
        cur=(R,ds,n)
        for _ in range(300):
            if time.time()-t0>50: break
            c=perturb(cur[1],Scap,dens)
            if c is None: continue
            R2,n2=R_of(c)
            if R2 is None: continue
            if R2>=cur[0]:
                cur=(R2,c,n2)
                if R2>best[0]: best=(R2,c,n2)
    print(f"{Scap:>8} {r:>9} {best[0]:>10.4f} {Sof(best[1]):>10.3f} {best[2]:>7}")
    print(f"         readings: {[round(float(d/min(best[1])),3) for d in best[1]]}")
