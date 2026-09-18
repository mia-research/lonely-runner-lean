"""R = d_min/D_final is d_min's OWN READING at the final scale.  Clearance requires every reading to
be >= 1 from a multiple of 8, so

    R mod 8  in  [1, 7]      i.e.   R in [1,7] u [9,15] u [17,23] u ...

R can never lie in (7,9), (15,17), ...  That explains the jump seen earlier: tau = R/8 went from
<= 0.63 straight to ~1.3, and (7,9) in R is exactly (0.875, 1.125) in tau.

Verify exhaustively, and check which bands are occupied.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor
import random
from collections import Counter
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def Rof(ds):
    ds=[F(d) for d in ds]
    if min(ds)<=0 or len(set(ds))!=len(ds): return None,None
    c=min(ds); t=TH/c; n=0
    while n<200000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return c*8*t, n
        t=max(nextOp(d,t) for d in b); n+=1
    return None,None
print("  verifying R mod 8 in [1,7] -- i.e. circDist(R/8) >= 1/8\n")
rng=random.Random(2027); viol=0; n=0; band=Counter(); mx=0; arg=None
KNOWN=[[30,74,96,127,159,175,224],[49,205,234,256,286,323,366],
       [28,69,95,123,154,172,220],[55,131,181,233,293,329,419],
       [46,107,146,194,241,268,344]]
for ds in KNOWN:
    R,d=Rof(ds)
    print(f"    {ds}  depth {d}  R = {R} = {float(R):.5f}   R mod 8 = {float(R%8):.5f}  "
          f"{'OK' if 1<=R%8<=7 else 'VIOLATION'}")
print()
for _ in range(20000):
    v=speeds(rng.sample(range(1,150),8))
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        R,d=Rof(ds)
        if R is None: continue
        n+=1
        if not (1<=R%8<=7): viol+=1
        band[int(R//8)]+=1
        if R>mx: mx,arg=R,(ds,d)
print(f"    {n} cascades sampled")
print(f"    violations of R mod 8 in [1,7] : {viol}")
print(f"    band occupancy (floor(R/8)) : {dict(sorted(band.items()))}")
print(f"    max R observed : {float(mx):.6f}  at depth {arg[1]}  {arg[0]}")
print()
print("  so R lies in [1,7] u [9,15] u [17,23] u ... and floor(R/8) counts the COMPLETE LAPS")
print("  d_min makes before isolation.  Bounding R = bounding that lap count.")
print()
print("  reachable bands, from everything measured so far:")
print(f"    band 0 (R in [1,7])   : {band.get(0,0)} random cascades")
print(f"    band 1 (R in [9,15])  : {band.get(1,0)} random + all five deep cases")
print(f"    band 2 (R in [17,23]) : {band.get(2,0)} -- never observed")
