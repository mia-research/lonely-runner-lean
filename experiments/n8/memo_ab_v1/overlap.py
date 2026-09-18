# The memo's proposed missing lemma is BOUNDED RETURN OVERLAP: how many setter-return debts
# can the same interval of cascade growth pay at once?  Closure needs mu < 2.033.
# But each runner's return intervals are DISJOINT and tile its own span, so mu should be ~ the
# number of runners that set repeatedly.  Measure it.
from fractions import Fraction as F
import math, random
n=8
def circ(x):
    f=x-(x.numerator//x.denominator); return min(f,1-f)
def trace(ds, maxs=4000):
    m=min(ds); t=F(1,n)/m; t0=t; rows=[]
    for _ in range(maxs):
        iw=[d for d in ds if circ(d*t)<F(1,n)]
        if not iw: return rows, t0, t, True
        best=None
        for d in iw:
            N=round(d*t); nx=(F(N)+F(1,n))/d
            if nx>t and (best is None or nx>best[0]): best=(nx,d,N)
        if best is None: return rows, t0, t, False
        nx,d,N=best; rows.append((d,N,t,nx)); t=nx
    return rows, t0, t, False
def b(P): return math.log((8*P+7)/(8*P+1)) if P>=1 else 0.0
def a(P): return math.log((8*P+1)/(8*P-1)) if P>=1 else 0.0
def audit(ds,label):
    rows,t0,tend,arr = trace([F(x) for x in ds])
    L = math.log(float(tend/t0))
    last={}; Bsum=0.0; Asum=0.0; setters=set()
    for i,(d,P,t,nx) in enumerate(rows):
        Asum += a(P); setters.add(d)
        if d in last: Bsum += b(last[d])
        last[d]=P
    print(f"{label}: {len(rows)} moves, {len(setters)} distinct setters, L_N = {L:.4f}")
    print(f"   S_N = sum a(P_j)        = {Asum:.4f}   (L_N <= S_N : {L<=Asum})")
    print(f"   sum over returns of b   = {Bsum:.4f}")
    print(f"   multiplicity mu = sumB/L_N = {Bsum/L:.3f}      (closure needs mu < 2.033)")
    print(f"   implied coefficient S_N/L_N = {Asum/L:.3f}      (closure needs < 1)")
audit([49,205,234,256,286,323,366], "6.7 climb subject 393")
audit([30,74,96,127,159,175,224],  "6.9 row subject 1")
rng=random.Random(5); mus=[]; coefs=[]
for _ in range(4000):
    ds=sorted(rng.sample(range(1,120),7))
    rows,t0,tend,arr = trace([F(x) for x in ds],maxs=400)
    if not arr or len(rows)<3: continue
    L=math.log(float(tend/t0))
    if L<=0: continue
    last={}; B=0.0; A=0.0
    for (d,P,t,nx) in rows:
        A+=a(P)
        if d in last: B+=b(last[d])
        last[d]=P
    mus.append(B/L); coefs.append(A/L)
mus.sort(); coefs.sort()
print(f"\nrandom sample, {len(mus)} cascades:")
print(f"   mu          : min {mus[0]:.3f}  median {mus[len(mus)//2]:.3f}  max {mus[-1]:.3f}")
print(f"   S_N/L_N     : min {coefs[0]:.3f}  median {coefs[len(coefs)//2]:.3f}  max {coefs[-1]:.3f}")
print(f"   cascades with mu < 2.033 : {sum(1 for x in mus if x<2.033)}/{len(mus)}")
print(f"   cascades with S_N/L_N < 1: {sum(1 for x in coefs if x<1)}/{len(coefs)}   <-- must be 0, since L_N <= S_N")
