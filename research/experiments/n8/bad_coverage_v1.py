"""Is the bad-interval coverage of (0, d_min] bounded away from 100%?
Bad set = U_{j,M>=1} ( d_j/(8M+1), d_j/(8M-1) )  intersected with (0, d_min].
A scale OUTSIDE it is a lonely instant, so 'coverage < 100%' IS Existence.
Reported ~56.2% asymptotically, from random arrangements.  Test it as a BOUND.
Exact Fraction; M capped, tail bounded analytically."""
import random
from fractions import Fraction as F
from math import gcd
MCAP=4000
def coverage(ds):
    m=min(ds); iv=[]
    for d in ds:
        d=F(d)
        for M in range(1,MCAP+1):
            lo=d/(8*M+1)
            if lo>=m: continue
            hi=min(d/(8*M-1), m)
            if hi>lo: iv.append((lo,hi))
            if hi<=0: break
    iv.sort()
    tot=F(0); cur_lo=None; cur_hi=None
    for lo,hi in iv:
        if cur_lo is None: cur_lo,cur_hi=lo,hi
        elif lo<=cur_hi: cur_hi=max(cur_hi,hi)
        else: tot+=cur_hi-cur_lo; cur_lo,cur_hi=lo,hi
    if cur_lo is not None: tot+=cur_hi-cur_lo
    # analytic tail bound for M > MCAP:  sum 2d/(64M^2-1) <= d/(32*MCAP)
    tail=sum(F(d)/(32*MCAP) for d in ds)
    return float(tot/m), float(tail/m)

print("=== A. random integer arrangements, by S band (reproduce the ~56%) ===")
rng=random.Random(7)
for lo,hi in [(2,4),(4,8),(8,16),(16,40),(40,120)]:
    cs=[]
    for _ in range(60):
        while True:
            v=sorted(rng.sample(range(0,200),8))
            ds=sorted(abs(v[j]-v[0]) for j in range(1,8))
            if ds[0]>0 and lo<=ds[-1]/ds[0]<=hi: break
        c,t=coverage(ds); cs.append(c)
    print(f"   S in [{lo},{hi}]: mean coverage {sum(cs)/len(cs):.4f}   max {max(cs):.4f}")

print()
print("=== B. the EXTREMAL sets found by the seven-flank search ===")
for ds in [[2,3,4,5,6,7,16],[2,3,4,5,6,7,32],[2,3,4,5,6,7,48],[1,3,7,14,21,49,56]]:
    c,t=coverage(ds)
    print(f"   ds={ds}  coverage {c:.6f}   (tail bound {t:.2e})")

print()
print("=== C. the hard cases on file ===")
for name,v,i in [("(1,31,75,97,128,160,176,225) r1",[1,31,75,97,128,160,176,225],0),
                 ("(27,70,...,393) r393",[27,70,107,137,159,188,344,393],7)]:
    ds=sorted(abs(v[j]-v[i]) for j in range(8) if j!=i)
    c,t=coverage(ds)
    print(f"   {name}: coverage {c:.6f}")

print()
print("=== D. adversarial: maximise coverage ===")
import time
rng=random.Random(5); t0=time.time(); best=(0,None)
while time.time()-t0<100:
    ds=sorted(rng.sample(range(1,40),7))
    g=0
    for d in ds: g=gcd(g,d)
    if g!=1: continue
    c,_=coverage(ds); cur=c
    for _ in range(120):
        if time.time()-t0>100: break
        cand=list(ds); k=rng.randrange(7)
        cand[k]=max(1,cand[k]+rng.choice([-2,-1,1,2]))
        cand=sorted(set(cand))
        if len(cand)!=7: continue
        g=0
        for d in cand: g=gcd(g,d)
        if g!=1: continue
        c2,_=coverage(cand)
        if c2>=cur:
            ds,cur=cand,c2
            if c2>best[0]: best=(c2,tuple(ds))
print(f"   BEST coverage found: {best[0]:.6f}   at ds = {best[1]}")
