# Owner's intuition: laps grow with the disparity between the speeds.
# Derivation: |y t - Q| < 1/n so Q > y t - 1/n; the cascade only increases so t >= t0 = 1/(n m).
#   => Q > (1/n)(rho - 1),  rho = y/m the ratio to the slowest.
# Consequence for the return constraint: the growth a setter supplies is
#   (Q + h)/(Q - h) = 1 + 2h/(Q - h),  DECREASING in Q.
# So FAST setters (large rho) supply LITTLE growth, and a return needs growth.
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
        nx,d,N=best; out.append((d,N,t)); t=nx
    return out, False, m

def audit(ds, label, show=True):
    tr, arr, m = trace([F(x) for x in ds])
    viol=0; ratios=[]
    for (d,Q,t) in tr:
        rho = d/m
        lb = (rho-1)/n
        if not (F(Q) > lb): viol+=1
        if lb > 0: ratios.append(float(F(Q)/lb))
    if show:
        print(f"{label}: {len(tr)} moves, Q > (rho-1)/8 violations: {viol}")
        if ratios:
            ratios.sort()
            print(f"   Q / lower bound : min {ratios[0]:.2f}  median {ratios[len(ratios)//2]:.2f}  max {ratios[-1]:.2f}")
    return viol, len(tr)

audit([49,205,234,256,286,323,366], "6.7 climb subject 393")
audit([30,74,96,127,159,175,224],  "6.9 row subject 1")
rng=random.Random(12); V=0; T=0
for _ in range(8000):
    ds=sorted(rng.sample(range(1,120),7))
    v,t = audit([F(x) for x in ds], "", show=False); V+=v; T+=t
print(f"random: {T} moves, violations {V}")
print()
# Does it bite?  In a RETURN window, what growth can the intervening setters supply,
# using ONLY the rho lower bound -- i.e. with no knowledge of the actual laps?
print("growth a setter of ratio rho can supply, from the bound alone:")
for rho in (1,2,4,8,16,32,64):
    Qlb = max(F(1), (F(rho)-1)/n)
    print(f"   rho={rho:3d}: Q >= {float(Qlb):.3f}  ->  factor <= {float((Qlb+h)/(Qlb-h)) if Qlb>h else float('inf'):.4f}")
