# The law: Q_j = rho_j * tau_j +- h, and tau_{j+1} = tau_j + (h - delta_j)/rho_j.
# CONSEQUENCE: (Q+h)/(Q-h) decreases in Q, so FAST setters (large rho) supply LITTLE growth.
# A return needs growth.  So returns should be paid for by SLOW setters.  Test that.
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

# [1] the two laws, exactly
bad1=bad2=tot=0
rng=random.Random(19)
for _ in range(4000):
    ds=sorted(rng.sample(range(1,120),7))
    tr,arr,m = trace([F(x) for x in ds],maxs=400)
    for (d,Q,t,nx) in tr:
        rho=d/m; tau=m*t; taun=m*nx; tot+=1
        if not (abs(rho*tau - F(Q)) < h): bad1+=1          # Q = rho*tau +- h
        inc = taun - tau
        if not (0 < inc <= 2*h/rho): bad2+=1               # tau increment in (0, 2h/rho]
print(f"[1] {tot} moves:  Q = rho*tau +- h  violations {bad1};  0 < d(tau) <= 2h/rho violations {bad2}")

# [2] do returns get paid for by SLOW setters?
def rhos_in_return_windows(ds):
    tr,arr,m = trace([F(x) for x in ds]); last={}; inwin=[]; allr=[]
    for i,(d,Q,t,nx) in enumerate(tr):
        allr.append(d/m)
        if d in last:
            j,_=last[d]
            inwin += [dd/m for (dd,QQ,tt,nn) in tr[j:i]]
        last[d]=(i,Q)
    return inwin, allr
for label, ds in (("6.7 climb", [49,205,234,256,286,323,366]),
                  ("6.9 row",   [30,74,96,127,159,175,224])):
    w,a = rhos_in_return_windows([F(x) for x in ds])
    w=sorted(float(x) for x in w); a=sorted(float(x) for x in a)
    print(f"[2] {label}: median rho of setters INSIDE return windows {w[len(w)//2]:.2f}"
          f"  vs ALL setters {a[len(a)//2]:.2f}")
W=[];A=[]
rng=random.Random(23)
for _ in range(6000):
    ds=sorted(rng.sample(range(1,120),7))
    tr,arr,m=trace([F(x) for x in ds],maxs=400)
    if not arr: continue
    last={}
    for i,(d,Q,t,nx) in enumerate(tr):
        A.append(float(d/m))
        if d in last:
            j,_=last[d]; W += [float(dd/m) for (dd,QQ,tt,nn) in tr[j:i]]
        last[d]=(i,Q)
W.sort(); A.sort()
print(f"[2] random: median rho inside return windows {W[len(W)//2]:.2f} vs all setters {A[len(A)//2]:.2f}"
      f"   (n_window={len(W)}, n_all={len(A)})")
print(f"    fraction of window setters with rho < 2 : {sum(1 for x in W if x<2)/len(W):.3f}"
      f"   vs all setters {sum(1 for x in A if x<2)/len(A):.3f}")
