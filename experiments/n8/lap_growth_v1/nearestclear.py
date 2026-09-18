# The n=4 proof's invariant was "tau <= (n-1)/n" -- the nearest stays in its FIRST window.
# That is NOT a framework requirement and it is FALSE at n=8 (tau reaches 1.283).
# The framework requirement is weaker and is what the argument actually needs:
#     the NEAREST runner is CLEAR at every cascade instant  (never in the way, never sets).
# tau can leave the first window by jumping OVER the blocked band (0,1/8)u(7/8,1).
# Test the weaker invariant, hard, including a hunt for counterexamples.
from fractions import Fraction as F
import random
n=8; h=F(1,n)
def circ(x):
    f=x-(x.numerator//x.denominator); return min(f,1-f)
def trace(ds, maxs=6000):
    m=min(ds); t=F(1,n)/m; taus=[]; blocked=0; sets=0
    for _ in range(maxs):
        iw=[d for d in ds if circ(d*t)<F(1,n)]
        taus.append(m*t)
        if circ(m*t) < F(1,n): blocked += 1
        if not iw: return taus, blocked, sets, True
        best=None
        for d in iw:
            N=round(d*t); nx=(F(N)+F(1,n))/d
            if nx>t and (best is None or nx>best[0]): best=(nx,d,N)
        if best is None: return taus, blocked, sets, False
        nx,d,N=best
        if d==m: sets+=1
        t=nx
    return taus, blocked, sets, False
for label, ds in (("6.7 climb", [49,205,234,256,286,323,366]),
                  ("6.9 row",   [30,74,96,127,159,175,224])):
    taus,b,s,arr = trace([F(x) for x in ds])
    print(f"{label}: {len(taus)} instants, max tau {float(max(taus)):.3f}, "
          f"instants where NEAREST is in the way: {b}, times it SET: {s}")
tot=0; anyblocked=0; worst=None
rng=random.Random(63)
for _ in range(40000):
    lo=rng.randrange(1,80)
    ds=sorted({lo}|set(rng.sample(range(lo+1,lo+600),6)))
    if len(ds)!=7: continue
    taus,b,s,arr = trace([F(x) for x in ds],maxs=800)
    if not arr: continue
    tot+=1
    if b>0:
        anyblocked+=1
        if worst is None: worst=(ds,b,s,float(max(taus)))
print(f"\nspread-biased search: {tot} arriving cascades")
print(f"   cascades where the NEAREST is ever in the way at an instant: {anyblocked}")
if worst: print(f"   example: ds={worst[0]}  blocked {worst[1]}x, set {worst[2]}x, max tau {worst[3]:.3f}")
# CONTROL: the invariant must be falsifiable -- check a runner that is NOT the nearest
ctl=0; tot2=0
rng=random.Random(64)
for _ in range(4000):
    ds=sorted(rng.sample(range(1,120),7))
    dsF=[F(x) for x in ds]; m=min(dsF); second=sorted(dsF)[1]
    t=F(1,n)/m; blocked2=0
    for _ in range(400):
        iw=[d for d in dsF if circ(d*t)<F(1,n)]
        if circ(second*t)<F(1,n): blocked2+=1
        if not iw: break
        best=None
        for d in iw:
            N=round(d*t); nx=(F(N)+F(1,n))/d
            if nx>t and (best is None or nx>best[0]): best=(nx,d,N)
        if best is None: break
        t=best[0]
    tot2+=1
    if blocked2>0: ctl+=1
print(f"   CONTROL, SECOND-slowest ever in the way: {ctl}/{tot2} cascades (0 would mean the test is blind)")
