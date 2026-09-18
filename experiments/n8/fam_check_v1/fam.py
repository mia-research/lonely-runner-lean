# Check the FAM memo's two checkable claims.
#  (1) SIMULTANEOUS EXHAUSTION: C_{j+1} >= U_i = (8N_i+1)/d_i for EVERY runner active at C_j,
#      not just the setter.  (Immediate from move taking the max -- but verify.)
#  (2) The mechanism FAM would rest on: each time d is active, its lap strictly increases.
#      If so, |S_d| is finite  <=>  d's lap is bounded  <=>  C is bounded.
from fractions import Fraction as F
import random
n=8
def circ(x):
    f=x-(x.numerator//x.denominator); return min(f,1-f)
def step(ds,t):
    iw=[d for d in ds if circ(d*t)<F(1,n)]
    if not iw: return None,None,iw
    best=None
    for d in iw:
        N=round(d*t); nx=(F(N)+F(1,n))/d
        if nx>t and (best is None or nx>best[0]): best=(nx,d,N)
    return (best[0],best[1],iw) if best else (None,None,iw)
bad1=bad2=tot=0; laps={}
rng=random.Random(5)
cases=[[49,205,234,256,286,323,366],[30,74,96,127,159,175,224]]
for _ in range(3000):
    cases.append(sorted(rng.sample(range(1,120),7)))
for ds0 in cases:
    ds=[F(x) for x in ds0]; m=min(ds); t=F(1,n)/m; lastlap={}
    for _ in range(600):
        nx,setter,iw = step(ds,t)
        if nx is None: break
        for d in iw:
            N=round(d*t)
            tot+=1
            # (1) the move reaches or passes EVERY active runner's current opening
            if not (nx >= (F(N)+F(1,n))/d): bad1+=1
            # (2) d's lap strictly increases between consecutive activities
            if d in lastlap and not (N > lastlap[d]): bad2+=1
            lastlap[d]=N
        t=nx
print(f"active-runner observations: {tot}")
print(f"  (1) C_next >= every active runner's own opening : violations {bad1}")
print(f"  (2) a runner's lap strictly increases between activities : violations {bad2}")
