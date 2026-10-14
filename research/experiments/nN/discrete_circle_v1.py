"""P: on the discrete circle Z/m the certificate form survives untouched, termination is
automatic (finite state space), and the conjecture becomes decidable per m.
Loneliness: for every disparity d, dist(d*t mod m, 0) >= m/n, dist(x)=min(x, m-x)."""
from itertools import combinations
from math import gcd
def dist(x,m): x%=m; return min(x,m-x)
def lonely(ds,t,m,n): return all(n*dist(d*t,m) >= m for d in ds)
def has_t(ds,m,n): return any(lonely(ds,t,m,n) for t in range(1,m))

print("=== 1. is the discrete statement TRUE?  exhaustive over small m, n ===")
print("   n   m     profiles   with NO lonely t   example failure")
for n in (3,4,5):
    for m in range(n, 26):
        tot=bad=0; ex=None
        for ds in combinations(range(1,m),n-1):
            if gcd(*ds, m) != 1 and len(ds)>1: pass
            tot+=1
            if not has_t(list(ds),m,n):
                bad+=1
                if ex is None: ex=ds
        if bad:
            print(f"   {n}  {m:3d} {tot:11d} {bad:17d}   {ex}")
print("   (rows shown only where failures occur)")

print()
print("=== 2. does the certificate form survive? ===")
print("   claim: t works  <=>  d*t mod m in [ceil(m/n), m - ceil(m/n)] for every d")
import math
bad=tot=0
for n in (3,4,5,6):
    for m in range(n,40):
        c=math.ceil(m/n)
        for ds in combinations(range(1,m),min(n-1,3)):
            for t in range(1,m):
                a=lonely(list(ds),t,m,n)
                b=all(c<=(d*t)%m<=m-c for d in ds)
                tot+=1
                if a!=b: bad+=1
print(f"   {tot} checks, {bad} mismatches")

print()
print("=== 3. termination: the state space is finite, so any forward walk on t must cycle ===")
print("   t ranges over Z/m: at most m-1 candidates, so the question is decidable by enumeration.")
print("   decidability is immediate; the content is whether a lonely t EXISTS, tested in 1.")
