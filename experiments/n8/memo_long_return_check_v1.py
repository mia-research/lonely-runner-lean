import random
from fractions import Fraction as F
n = 8
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
        rows.append((d,t,N,nxt)); t=nxt
    return rows, False

print("CHECK 1: does the memo's lambda_j = (8N_j+1)/s_j match the cascade's actual growth?")
rng=random.Random(31); ok=tot=0
for _ in range(3000):
    ds=sorted(F(x) for x in rng.sample(range(1,80),7))
    rows,arr=run(ds)
    if not arr: continue
    for d,t,N,nxt in rows:
        s = 8*d*t                      # memo's s_j
        lam_memo = (8*N+1)/s
        lam_actual = nxt/t
        tot+=1
        if lam_memo == lam_actual: ok+=1
print(f"  moves checked {tot}, lambda matches exactly: {ok}")
print()
print("CHECK 2: c_g over INTEGER speeds -- is c_4 really the smallest?")
cg={}
for _ in range(60000):
    ds=sorted(F(x) for x in rng.sample(range(1,100),7))
    rows,arr=run(ds)
    if not arr: continue
    last={}
    for i,(d,t,N,nxt) in enumerate(rows):
        if d in last:
            g=i-last[d]-1
            delta=d*t-N+F(1,n)
            if 0<delta: cg.setdefault(g,[]).append(delta)
        last[d]=i
print(f"  {'g':>3} {'returns':>8} {'inf delta observed':>22}")
for g in sorted(cg):
    if len(cg[g])<15: continue
    mn=min(cg[g])
    print(f"  {g:>3} {len(cg[g]):>8} {str(mn):>22}  = {float(mn):.3e}")
