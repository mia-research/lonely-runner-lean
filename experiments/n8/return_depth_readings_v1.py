import random
from fractions import Fraction as F
n = 8
def circq(x):
    f = x - (x.numerator // x.denominator); return min(f, 1-f)
def run(ds, maxsteps=400):
    m=min(ds); t=F(1,n)/m; rows=[]
    for _ in range(maxsteps):
        iw=[d for d in ds if circq(d*t) < F(1,n)]
        if not iw: return rows, True, m
        best=None
        for d in iw:
            N=round(d*t); nxt=(F(N)+F(1,n))/d
            if nxt>t and (best is None or nxt>best[0]): best=(nxt,d,N)
        if best is None: return rows, False, m
        nxt,d,N=best
        rows.append((d,t,N)); t=nxt
    return rows, False, m

print("TWO READINGS of 's_R = 8*N_R - 1 + 8*delta', both with 0 < delta < 1/4.")
print()
print("  (A) POSITION  : s = 8*d*t      -> delta = d*t - N + 1/8     [what I tested]")
print("  (B) READING   : s = d/d_min    -> delta = (d/d_min - 8N + 1)/8")
print()
rng=random.Random(21)
A=[]; B=[]
for _ in range(60000):
    ds=sorted(F(x) for x in rng.sample(range(1,120),7))
    rows,arr,m = run(ds)
    if not arr: continue
    last={}
    for i,(d,t,N) in enumerate(rows):
        if d in last and i-last[d]-1>=4:
            A.append(d*t-N+F(1,n))
            s = d/m
            NB = round(s/8)
            dB = (s - 8*NB + 1)/8
            if 0 < dB < F(1,4): B.append(dB)
        last[d]=i
print(f"  g>=4 returns found : {len(A)}")
if A: print(f"  (A) min delta      : {float(min(A)):.6e}   = {min(A)}")
if B: print(f"  (B) min delta      : {float(min(B)):.6e}   = {min(B)}   ({len(B)} of {len(A)} fall in (0,1/4))")
else: print(f"  (B) no returning setter has its READING in the band (0,1/4) -- reading (B) is empty here")
