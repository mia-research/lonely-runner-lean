import random, math
from fractions import Fraction as F
n = 8
# The circularity, written out.
#   (i)  log G  =  sum log lambda_j  <=  (2 - 8 c_*) * sum 1/s_j
#   (ii) return_growth: a runner setting at lap P returns only after growth
#        (P + 7/8)/(P + 1/8) = 1 + (3/4)/(P + 1/8), so per runner sum (3/4)/P <= log G,
#        i.e. sum 1/P <= (4/3) log G.  Over k runners, sum_j 1/N_j <= (4k/3) log G.
#   (iii) s_j = 8 d_j t_j ~ 8 N_j, so sum 1/s_j ~ (1/8) sum 1/N_j <= (k/6) log G.
# Compose (i) and (iii):
#        log G <= (2 - 8 c_*) * (k/6) * log G
# non-vacuous iff (2 - 8 c_*) k / 6 < 1, i.e.
#        c_* > 1/4 - 3/(4k).
print("THRESHOLD a depth floor would have to beat, from the circularity:")
print("     c_* > 1/4 - 3/(4k)")
for k in (3,4,5,6,7):
    thr = 0.25 - 0.75/k
    print(f"  k={k}: c_* > {thr:+.4f}" + ("   (negative -- no floor needed, 2k<n already closes it)" if thr<=0 else ""))
print()
print("So at k = 7 the needed floor is c_* > 1/4 - 3/28 = 1/7 = 0.1429, NOT c_* = 1/4.")
print("There IS room: the parametrisation allows delta up to 1/4 = 0.25.")
print()
# What is the actual floor?
def circq(x):
    f = x - (x.numerator // x.denominator); return min(f, 1-f)
def run(ds, maxsteps=400):
    m=min(ds); t=F(1,n)/m; rows=[]
    for _ in range(maxsteps):
        iw=[d for d in ds if circq(d*t) < F(1,n)]
        if not iw: return rows, True
        best=None
        for d in iw:
            N=round(d*t); nxt=(F(N)+F(1,n))/d
            if nxt>t and (best is None or nxt>best[0]): best=(nxt,d,N)
        if best is None: return rows, False
        nxt,d,N=best
        rows.append(d*t-N+F(1,n)); t=nxt
    return rows, False
rng=random.Random(41); allmin=[]
for _ in range(40000):
    ds=sorted(F(x) for x in rng.sample(range(1,100),7))
    rows,arr=run(ds)
    if arr and rows: allmin.append(min(rows))
allmin.sort()
print(f"ACTUAL depth over integer speeds [1,100], {len(allmin)} arriving cascades:")
print(f"  smallest delta seen anywhere : {float(allmin[0]):.6f}")
print(f"  1st percentile               : {float(allmin[len(allmin)//100]):.6f}")
print(f"  median over cascades         : {float(allmin[len(allmin)//2]):.6f}")
print(f"  needed at k=7                : 0.142857")
print()
print(f"  fraction of cascades whose MINIMUM depth already exceeds 1/7: "
      f"{sum(1 for x in allmin if x > F(1,7))/len(allmin):.3f}")
