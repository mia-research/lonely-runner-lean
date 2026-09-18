"""Q2  What DECREASES along the cascade and is bounded below?  n>2k has the potential Psi; at n=8
    it fails.  Test candidate monotone quantities on cascades that actually move.
Q3  Is the R-extremum a POINT or a CURVE?  Five searches converged on the same readings; nobody
    has asked whether the maximum is attained on a positive-dimensional family.
Exact Fraction."""
import random
from fractions import Fraction as F
from math import floor
import statistics as st
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def blockers(ds,t): return [d for d in ds if circd(d*t)<TH]
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d

print("=== Q2: candidate Lyapunov quantities along the cascade ===")
CASES=[[F(abs(x-1)) for x in (31,75,97,128,160,176,225)],
       [F(abs(x-393)) for x in (27,70,107,137,159,188,344)],
       [F(abs(x-1)) for x in (1975,5265,6910,8737,9589,11845,15135)]]
names=['nblockers','maxdepth','sumdepth','minclear','setter_reading','setter_lap']
rng=random.Random(8)
for _ in range(400):
    v=sorted(rng.sample(range(0,80),8)); i=rng.randrange(8)
    CASES.append(sorted(F(abs(v[j]-v[i])) for j in range(8) if j!=i))
mono={n:[0,0] for n in names}     # [non-increasing steps, total steps]
for ds in CASES:
    m=min(ds); t=TH/m; prev={}
    for _ in range(4000):
        b=blockers(ds,t)
        if not b: break
        nx={d:nextOp(d,t) for d in b}
        setter=max(b,key=lambda d:nx[d])
        cur={'nblockers':F(len(b)),
             'maxdepth':max(TH-circd(d*t) for d in b),
             'sumdepth':sum(TH-circd(d*t) for d in b),
             'minclear':min(circd(d*t) for d in ds),
             'setter_reading':setter/m,
             'setter_lap':F(floor(setter*t))}
        for k,val in cur.items():
            if k in prev:
                mono[k][1]+=1
                if val<=prev[k]: mono[k][0]+=1
        prev=cur
        t=nx[setter]
print(f"   {'quantity':>16} {'non-increasing':>15} {'steps':>7}")
for n in names:
    a,b=mono[n]
    print(f"   {n:>16} {a/max(b,1):>15.4f} {b:>7}")
print("   (a Lyapunov function would read 1.0000 and be bounded below)")

print()
print("=== Q3: is the R-extremum a point or a curve? ===")
def R_of(us,cap=4000):
    ds=sorted(us); m=min(ds); t=TH/m; n=0
    while n<cap:
        b=blockers(ds,t)
        if not b: return float(8*m*t)
        t=max(nextOp(d,t) for d in b); n+=1
    return None
EX=[F(1),F(2365,1000),F(3231,1000),F(4173,1000),F(5231,1000),F(5827,1000),F(7462,1000)]
R0=R_of(EX)
print(f"   extremal readings {[round(float(u),3) for u in EX]}   R = {R0:.5f}")
print(f"   {'coordinate':>11} {'-eps':>10} {'+eps':>10}   (eps = 0.002)")
eps=F(2,1000)
for c in range(1,7):
    out=[]
    for sgn in (-1,1):
        u=list(EX); u[c]=u[c]+sgn*eps
        r=R_of(u); out.append(r if r is not None else float('nan'))
    print(f"   {'u'+str(c+1):>11} {out[0]:>10.5f} {out[1]:>10.5f}")
print()
rng=random.Random(5)
for eps2 in [F(1,1000),F(2,1000),F(5,1000),F(1,100)]:
    keep=0; N=600; best=R0
    for _ in range(N):
        u=[EX[0]]+[EX[c]+F(rng.randint(-100,100),1)*eps2/100 for c in range(1,7)]
        r=R_of(sorted(u))
        if r is None: continue
        if r>best: best=r
        if r>=R0-0.01: keep+=1
    print(f"   eps = {float(eps2):.4f}: {keep}/{N} perturbations keep R within 0.01 of the max; best found {best:.5f}")
