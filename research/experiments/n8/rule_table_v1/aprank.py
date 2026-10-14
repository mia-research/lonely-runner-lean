# Departing from AP does not shift k -- it kills the nearest flank.  So does AP-defect predict
# WHICH FLANK nominates?  That would tie the owner's AP insight to the three-largest conjecture.
from math import gcd
import random, statistics
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def works(ds,b):
    for k in range(b):
        if all(clear(a,b,k) for a in ds): return True
    return False
def ap_defect(ds):
    s=sorted(ds); d=s[0]
    r=[s[i]/((i+1)*d) for i in range(len(s))]
    return statistics.pstdev(r)/statistics.mean(r)
rng=random.Random(23); rows=[]
for _ in range(20000):
    ds=sorted(rng.sample(range(1,120),7)); g=gcd(*ds); ds=tuple(x//g for x in ds)
    s=sorted(ds)
    wf=[i for i in range(7) if works(ds,s[i])]
    if not wf: continue
    rows.append((ap_defect(ds), min(wf), len(wf), ds))
B=[(0,.05),(.05,.15),(.15,.3),(.3,.5),(.5,1.0),(1.0,9)]
print(f"{'ap_defect':>14} {'n':>6} {'lowest working rank':>20} {'#working flanks':>17}")
for lo,hi in B:
    v=[r for r in rows if lo<=r[0]<hi]
    if len(v)<50: continue
    print(f"{lo:>6.2f}-{hi:<7.2f} {len(v):>6} {statistics.median(r[1] for r in v):>20.1f} "
          f"{statistics.median(r[2] for r in v):>17.1f}")
xs=[r[0] for r in rows]; ys=[float(r[1]) for r in rows]
mx=statistics.mean(xs); my=statistics.mean(ys)
num=sum((x-mx)*(y-my) for x,y in zip(xs,ys))
den=(sum((x-mx)**2 for x in xs)*sum((y-my)**2 for y in ys))**.5
print(f"\ncorrelation(ap_defect, lowest working flank rank) = {num/den:+.4f}")
ys2=[float(r[2]) for r in rows]; my2=statistics.mean(ys2)
num2=sum((x-mx)*(y-my2) for x,y in zip(xs,ys2))
den2=(sum((x-mx)**2 for x in xs)*sum((y-my2)**2 for y in ys2))**.5
print(f"correlation(ap_defect, number of working flanks)  = {num2/den2:+.4f}")
print()
# the extremal set: where does it sit?
for ds in [(1,2,3,4,5,6,7),(2,3,4,5,6,7,16),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13)]:
    s=sorted(ds); wf=[i for i in range(7) if works(ds,s[i])]
    print(f"   {str(ds):24s} ap_defect {ap_defect(ds):.4f}  working ranks {wf}")
