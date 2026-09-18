# tau CANCELS.  With Q_j = rho_j tau and P = rho_x tau, the return condition
#     (3/4)/(P + 1/8)  <  sum_j (1/4)/(Q_j - 1/8)
# becomes, to leading order,      3/rho_x  <  sum_{j in window} 1/rho_j
# Purely the speed disparities.  Test it, and test its consequence:
# for the SLOWEST runner rho_x = 1, so the window must supply sum 1/rho_j > 3 -- hard.
from fractions import Fraction as F
import random
n=8; h=F(1,n)
def circ(x):
    f=x-(x.numerator//x.denominator); return min(f,1-f)
def trace(ds, maxs=4000):
    m=min(ds); t=F(1,n)/m; out=[]
    for _ in range(maxs):
        iw=[d for d in ds if circ(d*t)<F(1,n)]
        if not iw: return out, True, m
        best=None
        for d in iw:
            N=round(d*t); nx=(F(N)+F(1,n))/d
            if nx>t and (best is None or nx>best[0]): best=(nx,d,N)
        if best is None: return out, False, m
        nx,d,N=best; out.append((d,N,t,nx)); t=nx
    return out, False, m
def audit(dsr, label):
    tr,arr,m = trace(dsr); last={}; ok=0; bad=0; ratios=[]; slow_returns=0; slow_sets=0
    for i,(d,Q,t,nx) in enumerate(tr):
        rx = d/m
        if rx == 1: slow_sets += 1
        if d in last:
            j,_=last[d]
            S = sum(F(1)/(dd/m) for (dd,QQ,tt,nn) in tr[j:i])
            if F(3)/rx < S: ok+=1
            else: bad+=1
            ratios.append(float((F(3)/rx)/S))
            if rx == 1: slow_returns += 1
        last[d]=(i,Q)
    ratios.sort()
    print(f"{label}: returns {ok+bad}, law holds {ok}, FAILS {bad}"
          + (f";  need/supplied med {ratios[len(ratios)//2]:.3f} max {ratios[-1]:.3f}" if ratios else ""))
    return slow_sets, slow_returns, len(tr)
audit([F(x) for x in [49,205,234,256,286,323,366]], "6.7 climb")
audit([F(x) for x in [30,74,96,127,159,175,224]],  "6.9 row")
OK=BAD=0; R=[]; SS=SR=MV=0
rng=random.Random(41)
for _ in range(6000):
    ds=[F(x) for x in sorted(rng.sample(range(1,120),7))]
    tr,arr,m=trace(ds,maxs=400)
    if not arr: continue
    last={}
    for i,(d,Q,t,nx) in enumerate(tr):
        rx=d/m; MV+=1
        if rx==1: SS+=1
        if d in last:
            j,_=last[d]
            S=sum(F(1)/(dd/m) for (dd,QQ,tt,nn) in tr[j:i])
            if F(3)/rx < S: OK+=1
            else: BAD+=1
            R.append(float((F(3)/rx)/S))
            if rx==1: SR+=1
        last[d]=(i,Q)
R.sort()
print(f"random: returns {OK+BAD}, law holds {OK}, FAILS {BAD}")
print(f"   need/supplied  median {R[len(R)//2]:.3f}  90th {R[int(.9*len(R))]:.3f}  max {R[-1]:.3f}  (<1 = satisfied)")
print(f"   SLOWEST runner (rho=1): set {SS} times of {MV}, and RETURNED {SR} times")
