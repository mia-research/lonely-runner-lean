# The requirement is  error/main < 1 - 1/M(ds), so the BINDING case is the smallest main term.
# Find min M exhaustively over primitive 7-subsets, and check M grows with sum(ds).
from math import gcd
from itertools import combinations
def win(a,b):
    s=a%8; lo=-(-(b-s)//8); hi=(7*b-s)//8
    return hi-lo+1
def exact_main(ds):
    tot=0.0
    for b in ds:
        t=float(b)
        for a in ds:
            if a==b: continue
            t *= win(a,b)/b
        tot+=t
    return tot
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def N(ds,b): return sum(1 for k in range(b) if all(clear(a,b,k) for a in ds))
best=None; rows=[]
for V in (12, 14, 16):
    mn=None
    for ds in combinations(range(1,V+1),7):
        if gcd(*ds)!=1: continue
        M=exact_main(ds)
        if mn is None or M<mn[0]: mn=(M,ds)
    print(f"  primitive 7-subsets of [1,{V}]: min exact main term {mn[0]:.4f} at ds={mn[1]}")
    if best is None or mn[0]<best[0]: best=mn
print()
M0=best[0]
print(f"GLOBAL FLOOR (over the ranges searched): M >= {M0:.4f} at {best[1]}")
print(f"  so the requirement error/main < 1 - 1/M is at worst  < {1-1/M0:.4f}")
print()
# exhaustive worst-case error/main over the small range where it is hardest
print("exhaustive over primitive 7-subsets of [1,14]: worst error/main")
worst=None; zeros=0; cnt=0
for ds in combinations(range(1,15),7):
    if gcd(*ds)!=1: continue
    cnt+=1
    M=exact_main(ds); T=sum(N(ds,b) for b in ds)
    if T==0: zeros+=1
    e=1-T/M
    if worst is None or e>worst[0]: worst=(e,ds,T,M)
print(f"  {cnt} sets, zeros {zeros}")
print(f"  worst error/main {worst[0]:.4f} at ds={worst[1]} (total {worst[2]}, main {worst[3]:.3f})")
print(f"  requirement at that set: < {1-1/worst[3]:.4f}   -> {'SATISFIED' if worst[0] < 1-1/worst[3] else 'VIOLATED'}")
print()
print(f"  margin: need {1-1/worst[3]:.4f}, have {worst[0]:.4f}, cushion factor {(1-1/worst[3])/worst[0]:.2f}x")
