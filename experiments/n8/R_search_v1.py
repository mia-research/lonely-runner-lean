"""With R computable directly from the profile, search far harder.

R_final = min{R >= 1 : all s_i.R mod 8 in [1,7]}.  s_1 = 1, so d_min's own bad set covers only
(7,9) and (15,17).  Band 2 (R >= 17) therefore requires the OTHER SIX disparities to cover
[1,7] u [9,15] completely -- 12 units, six combs of density 1/4 (18 units of bad measure available).

Search over profiles directly, in floats for speed, verifying the best in exact arithmetic.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from math import floor
import random
def clear(S,R):
    for s in S:
        m=(s*R)%8.0
        if m<1.0 or m>7.0: return False
    return True
def Rdir(S, RMAX=40.0):
    """smallest R >= 1 clear for all s in S; sweep right endpoints (8k+1)/s"""
    c=[1.0]
    for s in S:
        k=1
        while (8*k+1)/s<=RMAX:
            r=(8*k+1)/s
            if r>=1.0: c.append(r)
            k+=1
    c.sort()
    for R in c:
        if clear(S,R+1e-12): return R
    return None
def Rexact(ds, RMAX=60):
    c=F(min(ds)); S=[F(d)/c for d in ds]
    cand=[F(1)]
    for s in S:
        k=1
        while F(8*k+1)/s<=RMAX:
            r=F(8*k+1)/s
            if r>=1: cand.append(r)
            k+=1
    for R in sorted(set(cand)):
        if all(1<=(s*R)%8<=7 for s in S): return R
    return None
rng=random.Random(20260919)
best=(0,None)
N=0
for restart in range(4000):
    S=[1.0]+sorted(rng.uniform(1.05,7.95) for _ in range(6))
    cur=Rdir(S) or 0; stall=0
    for _ in range(3000):
        W=list(S); k=rng.randrange(1,7)
        W[k]+=rng.gauss(0,0.06)
        W=[1.0]+sorted(W[1:])
        if W[1]<=1.02 or W[6]>15.0 or any(W[i+1]-W[i]<0.02 for i in range(6)): continue
        v=Rdir(W) or 0; N+=1
        if v>cur: S,cur,stall=W,v,0
        elif v==cur: S,stall=W,stall+1
        else: stall+=1
        if stall>400: break
    if cur>best[0]: best=(cur,tuple(round(x,6) for x in S))
print(f"  {N} profile evaluations across 4000 restarts")
print(f"  max R (float search) : {best[0]:.6f}   band {int(best[0]//8)}")
print(f"    profile: " + " ".join(f"{x:.4f}" for x in best[1]))
# rationalise and verify exactly
c=2520
ds=sorted({int(round(c*x)) for x in best[1]})
if len(ds)==7:
    Re=Rexact(ds)
    print(f"\n  rationalised at c = {c}: {ds}")
    print(f"    exact R = {Re} = {float(Re):.6f}   band {int(float(Re)//8)}")
print(f"\n  band 2 (R >= 17) : {'REACHED' if best[0]>=17 else 'not reached'}")
print(f"  previous best R was 11.927057")
