# Where exactly does the proof stop?  Target.lean's own chain has every link proved EXCEPT a
# bound on the product in nearest_reading_recurrence:
#     m * t_N  <=  (1/n) * prod_{j<N} (Q_j + 1/n)/(Q_j - 1/n)
# So: how loose is that bound in practice, and can it EVER be bounded for an infinite cascade?
from fractions import Fraction as F
import random
n=8; h=F(1,n)
def circ(x):
    f=x-(x.numerator//x.denominator); return min(f,1-f)
def trace(ds, maxs=4000):
    m=min(ds); t=F(1,n)/m; rows=[]
    for _ in range(maxs):
        iw=[d for d in ds if circ(d*t)<F(1,n)]
        if not iw: return rows, True, m, t
        best=None
        for d in iw:
            N=round(d*t); nx=(F(N)+F(1,n))/d
            if nx>t and (best is None or nx>best[0]): best=(nx,d,N)
        if best is None: return rows, False, m, t
        nx,d,N=best; rows.append((d,N,t)); t=nx
    return rows, False, m, t
for label, ds in (("6.7 climb", [49,205,234,256,286,323,366]),
                  ("6.9 row",   [30,74,96,127,159,175,224])):
    rows, arr, m, tend = trace([F(x) for x in ds])
    prod=F(1); S=F(0)
    for (d,Q,t) in rows:
        prod *= (F(Q)+h)/(F(Q)-h); S += F(1)/F(Q)
    tau = m*tend
    print(f"{label}: {len(rows)} moves")
    print(f"   actual  m*t_N            = {float(tau):.4f}")
    print(f"   bound   (1/8)*prod       = {float(prod/n):.4f}     looseness x{float((prod/n)/tau):.1f}")
    print(f"   sum 1/Q_j                = {float(S):.4f}")
# Does the product diverge for a long cascade?  tau grows by at most 2h/rho <= 2h per move,
# so tau <= tau_0 + 2hN (LINEAR), hence Q_j grows at most linearly, hence sum 1/Q_j ~ log N,
# hence the product DIVERGES.  Check the linear-growth ceiling empirically.
rng=random.Random(77); worst=0; ratios=[]
for _ in range(20000):
    ds=sorted(rng.sample(range(1,120),7))
    rows,arr,m,tend = trace([F(x) for x in ds],maxs=600)
    if not arr or not rows: continue
    N=len(rows); tau=m*tend
    ratios.append(float(tau - F(1,n))/ (2*float(h)*N))   # actual growth vs the linear ceiling
ratios.sort()
print(f"\ntau growth as a fraction of its linear ceiling 2h*N, {len(ratios)} cascades:")
print(f"   max {ratios[-1]:.4f}   median {ratios[len(ratios)//2]:.4f}   (must be <= 1)")
print("   => tau grows AT MOST linearly, so Q_j does too, so sum 1/Q_j ~ log N diverges,")
print("      so the product diverges for an infinite cascade and the bound goes vacuous.")
