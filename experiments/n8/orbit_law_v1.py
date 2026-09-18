"""What makes the orbit predictable?

With the move in closed form the cascade is a 1-D deterministic map.  Setting x = t, clearance is
||a.x|| >= 1/8 for every reduced disparity a, so the cascade walks RIGHT from t0 = 1/(8 d_min)
through overlapping bad intervals and stops at the first clear point.

DEPTH = number of bad intervals crossed.  Disparity a contributes one bad interval per 1/a of t,
i.e. density a.  So over a walk of length (t_final - t0):

    depth ~ (t_final - t0) . sum_i a_i        (minus overlaps -- several blockers can share a step)

and since R = d_min/D_final = 8 d_min t_final,  t_final - t0 = (R-1)/(8 d_min), giving

    PREDICTION:   depth ~ (R - 1) . Sigma / 8,      Sigma = sum of readings d_i/d_min

Overlaps make this an UPPER bound on the crossing count and the cascade takes one step per
max-group, so expect depth <= prediction, with the ratio measuring overlap.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def cascade(ds):
    t0=TH/min(ds); t=t0; n=0; crossings=0
    while n<6000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return t,n,crossings
        crossings+=len(b)
        t=max(nextOp(d,t) for d in b); n+=1
    return None,None,None
rng=random.Random(1357)
rows=[]
for _ in range(2500):
    v=speeds(rng.sample(range(1,90),8))
    for i in range(8):
        ds=[F(abs(v[j]-v[i])) for j in range(8) if j!=i]
        dmin=min(ds)
        t,n,cr=cascade(ds)
        if t is None: continue
        R=dmin*8*t
        Sig=sum(d/dmin for d in ds)
        pred=float((R-1)*Sig/8)
        rows.append((n,pred,cr,float(R),float(Sig)))
import statistics as st
deep=[r for r in rows if r[0]>=1]
print(f"  {len(rows)} subjects, {len(deep)} with depth >= 1\n")
print(f"  {'depth':>6} {'n':>6} {'mean pred':>11} {'mean depth':>11} {'pred/depth':>11} {'crossings':>10}")
for k in range(1,9):
    g=[r for r in rows if r[0]==k]
    if len(g)<10: continue
    print(f"  {k:>6} {len(g):>6} {st.mean(r[1] for r in g):>11.3f} {k:>11} "
          f"{st.mean(r[1] for r in g)/k:>11.3f} {st.mean(r[2] for r in g):>10.2f}")
# correlation of prediction with depth
xs=[r[1] for r in deep]; ys=[float(r[0]) for r in deep]
mx,my=st.mean(xs),st.mean(ys)
cov=sum((a-mx)*(b-my) for a,b in zip(xs,ys))/len(xs)
r=cov/(st.pstdev(xs)*st.pstdev(ys))
print(f"\n  correlation(prediction, depth) over depth>=1 : {r:.4f}")
print(f"  correlation(crossings,  depth)               : ", end="")
xs2=[float(x[2]) for x in deep]; mx2=st.mean(xs2)
cov2=sum((a-mx2)*(b-my) for a,b in zip(xs2,ys))/len(xs2)
print(f"{cov2/(st.pstdev(xs2)*st.pstdev(ys)):.4f}")
print(f"\n  mean crossings / mean depth (blockers per step): {st.mean(r[2] for r in deep)/st.mean(ys):.4f}")
