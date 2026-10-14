# Owner: knowing the isolation points gives the clustering point via the AP arrangement.
# For an AP, positions at time t are an AP on the circle with generator d*t: clustering at
# generator 0, isolation at generator 1/8.  The cascade's bound t0 = 1/(8m) IS that point.
# PREDICTION: the further ds is from an AP, the further the working opening drifts from k=0.
from math import gcd
import random, statistics
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def firstk(ds,b):
    for k in range(b):
        if all(clear(a,b,k) for a in ds): return k
    return None
def ap_defect(ds):
    """how far the sorted set is from {d,2d,...,7d}: relative spread of d_i/(i*d_1)."""
    s=sorted(ds); d=s[0]
    r=[s[i]/((i+1)*d) for i in range(len(s))]
    return statistics.pstdev(r)/statistics.mean(r)
rng=random.Random(17)
rows=[]
for _ in range(20000):
    ds=sorted(rng.sample(range(1,120),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
    m=min(ds)
    k=firstk(ds,m)
    rows.append((ap_defect(ds), k, ds))
# exact APs
print("exact APs {d,2d,...,7d} -> normalise to {1..7}:")
print(f"   {(1,2,3,4,5,6,7)}: ap_defect {ap_defect((1,2,3,4,5,6,7)):.4f}, first k at nearest flank = {firstk((1,2,3,4,5,6,7),1)}")
print()
B=[(0,.05),(.05,.15),(.15,.3),(.3,.5),(.5,1.0),(1.0,9)]
print(f"{'ap_defect':>14} {'n':>6} {'k=0 works':>10} {'median k':>9} {'no k at nearest flank':>22}")
for lo,hi in B:
    v=[r for r in rows if lo<=r[0]<hi]
    if len(v)<50: continue
    ks=[r[1] for r in v if r[1] is not None]
    none=sum(1 for r in v if r[1] is None)
    z=sum(1 for k in ks if k==0)
    print(f"{lo:>6.2f}-{hi:<7.2f} {len(v):>6} {z/len(v):>10.3f} "
          f"{(statistics.median(ks) if ks else float('nan')):>9.1f} {none/len(v):>22.3f}")
print()
corr_n=[r for r in rows if r[1] is not None]
xs=[r[0] for r in corr_n]; ys=[float(r[1]) for r in corr_n]
mx=statistics.mean(xs); my=statistics.mean(ys)
num=sum((x-mx)*(y-my) for x,y in zip(xs,ys))
den=(sum((x-mx)**2 for x in xs)*sum((y-my)**2 for y in ys))**.5
print(f"correlation(ap_defect, first working k) = {num/den:+.4f}   over {len(corr_n)} sets")
