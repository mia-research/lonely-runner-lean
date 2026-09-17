# What does return_needs_moves actually give at n=8, and does it hold on real cascades?
#   a return from lap P after m moves needs   (P + 7/8)/(P + 1/8) < (9/7)^m
from fractions import Fraction as F
n = 8; h = F(1,n); R = (1+h)/(1-h)          # 9/7
print("minimum intervening moves before a runner at lap P may be in the way again:")
for P in range(0, 9):
    need = (F(P)+1-h)/(F(P)+h)
    m = 0
    while R**m <= need: m += 1
    print(f"   P={P}: cost {float(need):.4f}  -> m >= {m}" + ("   (no constraint)" if m<=1 else ""))
print()
def circ(x):
    f = x - (x.numerator // x.denominator); return min(f, 1-f)
def trace(ds, maxs=4000):
    a=min(ds); t=F(1,n)/a; out=[]
    for _ in range(maxs):
        iw=[d for d in ds if circ(d*t) < F(1,n)]
        if not iw: return out, True
        best=None
        for d in iw:
            N=round(d*t); nx=(F(N)+F(1,n))/d
            if nx>t and (best is None or nx>best[0]): best=(nx,d,N)
        if best is None: return out, False
        nx,d,N = best; out.append((d,N,t,nx)); t=nx
    return out, False

import random
def check(ds, label):
    tr, arr = trace([F(x) for x in ds])
    # for each setter, the gap in MOVES between consecutive settings, and the lap it left from
    last = {}
    viol = 0; tested = 0; tight = []
    for i,(d,N,t,nx) in enumerate(tr):
        if d in last:
            j, P = last[d]
            m = i - j                                  # moves between the two settings
            need = (F(P)+1-h)/(F(P)+h)
            tested += 1
            if not (need < R**m): viol += 1
            mreq = 0
            while R**mreq <= need: mreq += 1
            tight.append((P, m, mreq))
        last[d] = (i, N)
    slack = [m-mreq for _,m,mreq in tight]
    print(f"{label}: {len(tr)} moves, arrived={arr}, returns tested {tested}, VIOLATIONS {viol}")
    if tight:
        print(f"   observed gap minus required, min {min(slack)}  median {sorted(slack)[len(slack)//2]}  max {max(slack)}")
        print(f"   returns where the bound is TIGHT (gap == required): {sum(1 for s in slack if s==0)}")
check([49,205,234,256,286,323,366], "6.7 climb subject 393")
check([30,74,96,127,159,175,224],  "6.9 row subject 1")
rng=random.Random(31); V=0; T=0; S=[]
for _ in range(20000):
    ds=sorted(rng.sample(range(1,120),7))
    tr,arr = trace([F(x) for x in ds], maxs=600)
    if not arr: continue
    last={}
    for i,(d,N,t,nx) in enumerate(tr):
        if d in last:
            j,P = last[d]; m=i-j; need=(F(P)+1-h)/(F(P)+h); T+=1
            if not (need < R**m): V+=1
            mreq=0
            while R**mreq <= need: mreq+=1
            S.append(m-mreq)
        last[d]=(i,N)
S.sort()
print(f"\nrandom sample: {T} returns tested, VIOLATIONS {V}")
if S: print(f"   slack min {S[0]}  1% {S[len(S)//100]}  median {S[len(S)//2]};  tight returns {S.count(0)}")
