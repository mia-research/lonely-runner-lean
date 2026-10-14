# The exhaustive worst case was (1,3,4,5,7,18,40): a tight small cluster plus two spread
# elements.  Search THAT SHAPE hard - does the cushion (M-1)/error drop below 1?
from math import gcd
from itertools import combinations
import random
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
def T(ds): return sum(sum(1 for k in range(b) if all(clear(a,b,k) for a in ds)) for b in ds)
best=None; nT1=0; nfail=0; n=0
rng=random.Random(99)
# shape: 5 from a small cluster, 2 spread
for _ in range(120000):
    lo=sorted(rng.sample(range(1,14),5))
    hi=sorted(rng.sample(range(14,130),2))
    ds=tuple(lo+hi)
    g=0
    for x in ds: g=gcd(g,x)
    ds=tuple(x//g for x in ds)
    if len(set(ds))!=7: continue
    n+=1
    M=exact_main(ds); t=T(ds)
    if t<=1: nT1+=1
    if M<=t: continue
    c=(M-1)/(M-t)
    if c<1: nfail+=1
    if best is None or c<best[0]: best=(c,ds,t,M)
print(f"targeted shape (5 clustered + 2 spread): {n} sets")
print(f"  minimum cushion: {best[0]:.4f}x at ds={best[1]}  T={best[2]}  M={best[3]:.3f}")
print(f"     error/M = {(best[3]-best[2])/best[3]:.4f}   requirement < {1-1/best[3]:.4f}")
print(f"  sets where the FIRST-MOMENT bound fails (cushion < 1): {nfail}")
print(f"  sets with T <= 1 (door 4 itself tight): {nT1}")
print()
# and 4 clustered + 3 spread
best2=None; nfail2=0; n2=0
for _ in range(120000):
    lo=sorted(rng.sample(range(1,12),4))
    hi=sorted(rng.sample(range(12,160),3))
    ds=tuple(lo+hi)
    g=0
    for x in ds: g=gcd(g,x)
    ds=tuple(x//g for x in ds)
    if len(set(ds))!=7: continue
    n2+=1
    M=exact_main(ds); t=T(ds)
    if M<=t: continue
    c=(M-1)/(M-t)
    if c<1: nfail2+=1
    if best2 is None or c<best2[0]: best2=(c,ds,t,M)
print(f"shape (4 clustered + 3 spread): {n2} sets")
print(f"  minimum cushion: {best2[0]:.4f}x at ds={best2[1]}  T={best2[2]}  M={best2[3]:.3f}")
print(f"  first-moment failures: {nfail2}")
