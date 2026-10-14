import random
from fractions import Fraction as F
n = 8
def circq(x):
    f = x - (x.numerator // x.denominator); return min(f, 1-f)
def run_exact(ds, maxsteps=400):
    m=min(ds); t=F(1,n)/m; rows=[]; prev=None
    for _ in range(maxsteps):
        iw=[d for d in ds if circq(d*t) < F(1,n)]
        if not iw: return rows, True
        best=None
        for d in iw:
            N=round(d*t); nxt=(F(N)+F(1,n))/d
            if nxt>t and (best is None or nxt>best[0]): best=(nxt,d,N)
        if best is None: return rows, False
        nxt,d,N=best
        rows.append((d,(d*t-N)+F(1,n),prev)); prev=d; t=nxt
    return rows, False

# CLAIM TO TEST: for INTEGER speeds, t is always (N'+1/8)/d' for the previous setter d',
# so delta = d*t - N + 1/8 has denominator dividing 8*d'. Hence delta > 0 implies
#            delta >= 1/(8*d'),
# a floor set by the PREVIOUS SETTER's speed -- not a universal constant.
rng=random.Random(9)
tested=0; ok=0; viol=[]; ratios=[]
for _ in range(30000):
    ds=sorted(F(x) for x in rng.sample(range(1,120),7))
    rows,arr=run_exact(ds)
    if not arr: continue
    for d,dl,prev in rows:
        if prev is None or dl==0: continue
        tested+=1
        bound=F(1,8*int(prev))
        if dl>=bound: ok+=1
        else: viol.append((d,dl,prev,bound))
        ratios.append(float(dl/bound))
print(f"moves tested (integer speeds, exact arithmetic) : {tested}")
print(f"  delta >= 1/(8 * previous setter's speed)      : {ok}")
print(f"  violations                                    : {len(viol)}")
if viol:
    for v in viol[:3]: print(f"    d={v[0]} delta={v[1]} prev={v[2]} bound={v[3]}")
else:
    ratios.sort()
    print(f"  delta / bound : min {ratios[0]:.3f}  median {ratios[len(ratios)//2]:.1f}")
    print()
    print("  So for integer speeds the floor is REAL but is 1/(8*d'), set by the previous")
    print("  setter. Bounded speeds give a floor; unbounded speeds do not. There is no")
    print("  universal c_*, and the continuous counterexamples are the d' -> infinity limit.")
