"""Owner, 2026-09-18: Theorem 6.2(b) proves the cascade lands on the EARLIEST lonely instant,
but Existence only needs SOME lonely instant.  Is first-ness costing us the move count?
Compare, on the same subjects: cascade moves (to the FIRST) vs the smallest opening index at
ANY flank that is lonely (to ANY).  Exact Fraction."""
import random
from fractions import Fraction as F
from math import floor, ceil
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def inWay(d,t): return circd(d*t)<TH
def nextOp(d,t):
    k=ceil(d*t-TH)
    if k<0:k=0
    while F(k,1)+TH<d*t:k+=1
    return (F(k,1)+TH)/d
def cascade(ds,cap=5000):
    m=min(ds); t=TH/m; n=0
    while n<cap:
        b=[d for d in ds if inWay(d,t)]
        if not b: return t,n,float(8*m*t)
        t=max(nextOp(d,t) for d in b); n+=1
    return None,n,None
def min_k_any(ds,KMAX=2000):
    for k in range(KMAX+1):
        kk=F(k)+TH
        for e in ds:
            t=kk/e
            if all(circd(d*t)>=TH for d in ds): return k,e,t
    return None,None,None

HARD=[("(1,31,75,97,128,160,176,225)",[1,31,75,97,128,160,176,225],0),
      ("(27,70,107,137,159,188,344,393)",[27,70,107,137,159,188,344,393],7),
      ("(1,1975,5265,6910,8737,9589,11845,15135)",[1,1975,5265,6910,8737,9589,11845,15135],0),
      ("(11,21,22,23,26,34,35,40)",[11,21,22,23,26,34,35,40],6)]
print("THE HARD CASES ON FILE  -- speeds as speeds, no zero runner")
print(f"  {'arrangement':>42} {'subject':>8} {'cascade moves':>14} {'min k any flank':>16} {'flank e':>10}")
for name,v,i in HARD:
    v=[F(x) for x in v]
    ds=sorted(abs(v[j]-v[i]) for j in range(8) if j!=i)
    t,n,R=cascade(ds)
    k,e,tk=min_k_any(ds)
    print(f"  {name:>42} {str(v[i]):>8} {n:>14} {k:>16} {str(e):>10}")

print()
print("the R-extremal arrangement (no zero speed):")
v=[F(1),F(2),F(3365,1000),F(4231,1000),F(5173,1000),F(6231,1000),F(6827,1000),F(8462,1000)]
print("   speeds", [round(float(x),3) for x in v])
print(f"  {'subject':>10} {'S':>8} {'cascade moves':>14} {'R':>8} {'min k any flank':>16}")
for i in range(8):
    ds=sorted(abs(v[j]-v[i]) for j in range(8) if j!=i)
    t,n,R=cascade(ds); k,e,tk=min_k_any(ds)
    print(f"  {float(v[i]):>10.3f} {float(max(ds)/min(ds)):>8.3f} {n:>14} {R:>8.4f} {k:>16}")

print()
print("POPULATION: hard band S in [7,8], 20000 subjects")
rng=random.Random(9); D=1000
mv=[];kk=[]
for _ in range(20000):
    us=[F(1)]; top=F(rng.randint(7*D,8*D),D)
    for _ in range(5): us.append(F(rng.randint(D,int(top*D)),D))
    us.append(top)
    ds=sorted(set(us))
    if len(ds)!=7: continue
    t,n,R=cascade(ds)
    if t is None: continue
    k,e,_=min_k_any(ds,400)
    if k is None: continue
    mv.append(n); kk.append(k)
import statistics as st
print(f"   cascade moves (to the FIRST):  mean {st.mean(mv):.2f}   max {max(mv)}")
print(f"   min k any flank (to ANY)    :  mean {st.mean(kk):.2f}   max {max(kk)}")
