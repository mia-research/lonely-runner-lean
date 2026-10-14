import random, math
from fractions import Fraction as F
n = 8
def circq(x):
    f = x - (x.numerator // x.denominator); return min(f, 1-f)
def run(ds, maxsteps=400):
    m=min(ds); t0=F(1,n)/m; t=t0; rows=[]
    for _ in range(maxsteps):
        iw=[d for d in ds if circq(d*t) < F(1,n)]
        if not iw: return rows, True, t0, t
        best=None
        for d in iw:
            N=round(d*t); nxt=(F(N)+F(1,n))/d
            if nxt>t and (best is None or nxt>best[0]): best=(nxt,d,N)
        if best is None: return rows, False, t0, t
        nxt,d,N=best
        rows.append((d,t,N)); t=nxt
    return rows, False, t0, t

# The circle:  log G <= 2 * sum(1/s_j)   and   sum(1/s_j) <= (k/6) log G.
# Composed constant 2k/6 = k/3 = 2.33 at k=7, needs < 1.
# How TIGHT is the second inequality in practice?  If the true ratio is far below k/6,
# a sharper lap bound could still close the circle; if it is near k/6, there is no room.
rng=random.Random(43); ratios=[]; lhs=[]
for _ in range(30000):
    ds=sorted(F(x) for x in rng.sample(range(1,100),7))
    rows,arr,t0,tf = run(ds)
    if not arr or len(rows)<4: continue
    G = float(tf/t0)
    if G <= 1.0001: continue
    S = sum(1.0/float(8*d*t) for d,t,N in rows)
    ratios.append(S/math.log(G))
    lhs.append(2*S/math.log(G))
ratios.sort(); lhs.sort()
k=7
print(f"cascades used : {len(ratios)}")
print(f"  bound says   sum(1/s_j) / log G  <=  k/6 = {k/6:.3f}")
print(f"  measured     median {ratios[len(ratios)//2]:.3f}   90th {ratios[int(.9*len(ratios))]:.3f}   max {ratios[-1]:.3f}")
print()
print(f"  the composed constant 2*sum(1/s)/log G must be < 1 to close the circle:")
print(f"  measured     median {lhs[len(lhs)//2]:.3f}   10th {lhs[int(.1*len(lhs))]:.3f}   min {lhs[0]:.3f}")
print(f"  fraction of cascades with composed constant < 1 : {sum(1 for x in lhs if x<1)/len(lhs):.3f}")
