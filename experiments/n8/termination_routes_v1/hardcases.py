# The previous sample was UNDERPOWERED: median 0 moves means it mostly drew cases that
# terminate at the bound.  RETURN_CORRECTION_v3 names arrangements where the nearest
# runner's lap count reaches ~10.3, so the invariant must fail where that sample never went.
from fractions import Fraction as F
import random
n = 8
def circ(x):
    f = x - (x.numerator // x.denominator); return min(f, 1-f)
def run(ds, maxsteps=4000):
    a=min(ds); t=F(1,n)/a; taus=[F(1,n)]; setters=[]
    for _ in range(maxsteps):
        iw=[d for d in ds if circ(d*t) < F(1,n)]
        if not iw: return setters, taus, True
        best=None
        for d in iw:
            N=round(d*t); nxt=(F(N)+F(1,n))/d
            if nxt>t and (best is None or nxt>best[0]): best=(nxt,d)
        if best is None: return setters, taus, False
        t=best[0]; setters.append(best[1]); taus.append(a*t)
    return setters, taus, False

named = {
 "6.7 climb (27,70,107,137,159,188,344,393), subject 393":
    [49,205,234,256,286,323,366],
 "6.9 row (1,31,75,97,128,160,176,225), subject 1":
    [30,74,96,127,159,175,224],
}
W = F(n-1, n)
for name, ds in named.items():
    s, taus, arr = run([F(x) for x in ds])
    mt = max(taus)
    print(f"{name}")
    print(f"   arrived={arr}  moves={len(s)}  max tau = a*t = {float(mt):.3f}"
          f"   first window ends {float(W):.3f}   -> nearest {'STAYED' if mt<=W else 'LEFT'} its first window")
    print(f"   distinct setters {len(set(s))} of 7;  repeats {len(s)-len(set(s))}")
print()
# biased search: large spread is where the hard cases live
rng=random.Random(2024); left=0; tot=0; worst=None; mv=[]
for _ in range(60000):
    lo = rng.randrange(1, 60)
    ds = sorted({lo} | set(rng.sample(range(lo+1, lo+420), 6)))
    if len(ds)!=7: continue
    s, taus, arr = run([F(x) for x in ds], maxsteps=600)
    if not arr: continue
    tot+=1; mt=max(taus); mv.append(len(s))
    if mt > W:
        left+=1
        if worst is None or mt > worst[0]: worst=(mt, ds, len(s))
mv.sort()
print(f"spread-biased sample: {tot} arriving cascades, moves med {mv[len(mv)//2]} max {mv[-1]}")
print(f"   cascades where the NEAREST leaves its first clear window: {left}/{tot} = {left/tot:.4f}")
if worst: print(f"   worst max tau = {float(worst[0]):.3f} at ds={worst[1]} ({worst[2]} moves)")
