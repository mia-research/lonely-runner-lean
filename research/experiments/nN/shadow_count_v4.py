"""Two-pivot bound from PAIRWISE data only, and the shape of what survives."""
from math import gcd
from itertools import combinations
N=8
def bset(d,e,n=N): return frozenset(j for j in range(e) if not (e<=(d*(n*j+1))%(n*e)<=(n-1)*e))
def bnds(ds,e,n=N):
    B=[bset(d,e,n) for d in ds if d!=e]
    if not B: return 0,0,0,0
    union=len(set().union(*B)); b0=sum(map(len,B))
    b1=min(len(P)+sum(len(X)-len(X&P) for k,X in enumerate(B) if B[i] is not X or k!=i)
           for i,P in enumerate(B)) if False else \
       min(len(B[i])+sum(len(B[k])-len(B[k]&B[i]) for k in range(len(B)) if k!=i) for i in range(len(B)))
    b2=b1
    for i in range(len(B)):
        for j in range(i+1,len(B)):
            base=len(B[i])+len(B[j])-len(B[i]&B[j])
            rest=sum(len(B[k])-max(len(B[k]&B[i]),len(B[k]&B[j])) for k in range(len(B)) if k not in (i,j))
            b2=min(b2,base+rest)
    return b0,b1,b2,union

print("=== A. soundness of the two-pivot bound ===")
bad=0;tot=0
for ds in combinations(range(1,16),7):
    if ds[0]!=1: continue
    for e in ds:
        b0,b1,b2,u=bnds(list(ds),e); tot+=1
        if b2<u: bad+=1
print(f"   flank-instances {tot};  violations (b2 < truth): {bad}")

print()
print("=== B. reach in the middle: union -> pivot -> two-pivot -> truth ===")
mid=c0=c1=c2=ct=0; survivors=[]
for ds in combinations(range(1,22),7):
    if ds[0]!=1: continue
    L=list(ds); M=sum(1 for d in L if d%N==0)
    if not (1<=M<=len(L)-2): continue
    mid+=1
    r=[(e,)+bnds(L,e) for e in L]
    f0=any(b0<e for e,b0,b1,b2,u in r); f1=any(b1<e for e,b0,b1,b2,u in r)
    f2=any(b2<e for e,b0,b1,b2,u in r); ft=any(u<e  for e,b0,b1,b2,u in r)
    c0+=f0; c1+=f1; c2+=f2; ct+=ft
    if ft and not f2: survivors.append((ds,M,r))
print(f"   middle sets                    : {mid}")
print(f"   Thm 15.50 union bound          : {c0}")
print(f"   one-pivot bound                : {c1}")
print(f"   two-pivot bound (pairwise data): {c2}")
print(f"   truth                          : {ct}")

print()
print("=== C. how do the survivors fail?  (is the bound landing exactly on e?) ===")
import collections
off=collections.Counter()
for ds,M,r in survivors:
    best=min((b2-e) for e,b0,b1,b2,u in r)
    off[best]+=1
print("   min over flanks of (bound - e), needs < 0:")
for k in sorted(off)[:8]: print(f"     {k:+3d} : {off[k]}")
print(f"   survivors: {len(survivors)}")
for ds,M,r in survivors[:5]:
    e,b0,b1,b2,u=min(r,key=lambda t:t[3]-t[0])
    print(f"     {ds} M={M}: e={e} union={b0} pivot={b1} two-pivot={b2} TRUTH={u}")
