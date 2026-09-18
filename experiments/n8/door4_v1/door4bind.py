# Door 4 holds iff total = sum_b N(b) >= 1, i.e. error <= M - 1.
# Find the genuinely binding sets: smallest TOTAL, and smallest cushion (M-1)/error.
from math import gcd
from itertools import combinations
def win(a,b):
    s=a%8; lo=-(-(b-s)//8); hi=(7*b-s)//8
    return hi-lo+1
def exact_main(ds):
    t=0.0
    for b in ds:
        x=float(b)
        for a in ds:
            if a!=b: x *= win(a,b)/b
        t+=x
    return t
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def N(ds,b): return sum(1 for k in range(b) if all(clear(a,b,k) for a in ds))
for V in (14, 17):
    rows=[]
    for ds in combinations(range(1,V+1),7):
        if gcd(*ds)!=1: continue
        M=exact_main(ds); T=sum(N(ds,b) for b in ds)
        rows.append((T,M,ds))
    rows.sort(key=lambda r:(r[0], r[1]))
    mn=rows[0][0]
    print(f"[1,{V}]: {len(rows)} primitive sets.  minimum total = {mn}")
    for T,M,ds in rows[:5]:
        err=M-T
        print(f"     ds={ds} total {T}  main {M:.3f}  error {err:.3f}  err/M {err/M:.4f}  need < {1-1/M:.4f}  cushion {(M-1)/err:.3f}x")
    cush=sorted(((M-1)/(M-T) if M>T else 9e9, ds, T, M) for T,M,ds in rows)
    print(f"   SMALLEST cushion: {cush[0][0]:.3f}x at ds={cush[0][1]} (total {cush[0][2]}, main {cush[0][3]:.3f})")
    print(f"   sets with total 1: {sum(1 for T,_,_ in rows if T==1)};  total 0: {sum(1 for T,_,_ in rows if T==0)}")
    print()
