# return_needs_growth takes ANY C.  Instantiate it with the REAL intervening laps:
#     (P + 1 - h)/(P + h)  <  prod_{j in window} (Q_j + h)/(Q_j - h)
# If that is tight, the lemma says the intervening laps must be SMALL -- a real constraint.
from fractions import Fraction as F
import random
n=8; h=F(1,n)
def circ(x):
    f=x-(x.numerator//x.denominator); return min(f,1-f)
def trace(ds, maxs=4000):
    a=min(ds); t=F(1,n)/a; out=[]
    for _ in range(maxs):
        iw=[d for d in ds if circ(d*t)<F(1,n)]
        if not iw: return out, True
        best=None
        for d in iw:
            N=round(d*t); nx=(F(N)+F(1,n))/d
            if nx>t and (best is None or nx>best[0]): best=(nx,d,N)
        if best is None: return out, False
        nx,d,N=best; out.append((d,N)); t=nx
    return out, False
def audit(ds,label):
    tr,arr=trace([F(x) for x in ds]); last={}; ratios=[]; viol=0
    for i,(d,N) in enumerate(tr):
        if d in last:
            j,P=last[d]
            need=(F(P)+1-h)/(F(P)+h)
            prod=F(1)
            for (dd,Q) in tr[j:i]:
                prod *= (F(Q)+h)/(F(Q)-h)
            if not (need < prod): viol+=1
            ratios.append(float(need/prod))       # 1.0 = exactly tight
        last[d]=(i,N)
    ratios.sort()
    if ratios:
        print(f"{label}: returns {len(ratios)}, violations {viol}")
        print(f"   need/supplied  max {ratios[-1]:.4f}  median {ratios[len(ratios)//2]:.4f}  min {ratios[0]:.4f}   (1.0 = tight)")
audit([49,205,234,256,286,323,366],"6.7 climb subject 393")
audit([30,74,96,127,159,175,224], "6.9 row subject 1")
rng=random.Random(8); allr=[]; V=0
for _ in range(20000):
    ds=sorted(rng.sample(range(1,120),7))
    tr,arr=trace([F(x) for x in ds],maxs=600)
    if not arr: continue
    last={}
    for i,(d,N) in enumerate(tr):
        if d in last:
            j,P=last[d]; need=(F(P)+1-h)/(F(P)+h); prod=F(1)
            for (dd,Q) in tr[j:i]: prod*=(F(Q)+h)/(F(Q)-h)
            if not (need<prod): V+=1
            allr.append(float(need/prod))
        last[d]=(i,N)
allr.sort()
print(f"\nrandom sample: {len(allr)} returns, violations {V}")
print(f"   need/supplied  max {allr[-1]:.4f}  90th {allr[int(.9*len(allr))]:.4f}  median {allr[len(allr)//2]:.4f}")
print(f"   returns using >50% of the supplied growth: {sum(1 for r in allr if r>0.5)}/{len(allr)}")
