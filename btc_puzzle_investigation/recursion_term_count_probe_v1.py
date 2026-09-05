#!/usr/bin/env python3
"""
Which recursion gives ~10-11 terms at 246 bits? The dataset's (validated) recursion
saturates at 4-5. Compare candidate recursions' term counts so we test the RIGHT one:
  (S)  simple/CSV:  D_i=floor(A/|err|), term=sign*floor(A/D_i)   [= dataset D_terms]
  (N256) nested (n,k,D), denom<=256: recursively best-approx the residual each scale
  (N2048) nested, denom<=2048
  (Sbig)  simple but with larger effective granularity (term=sign*|err|//2^g)
Report term-count distribution at N=246 for each. No ECC needed (pure decomposition).
"""
import random
from math import gcd
rnd=random.Random(7)

def best_nk_bound(v,b,NMAX):
    """best rational approx k/n of u=(v-A)/A, v in [A,2A), denom<=NMAX. exact."""
    A=1<<(b-1); num=v-A; best=None
    for n in range(1,NMAX+1):
        k=(2*n*num+A)//(2*A); k=0 if k<0 else (n if k>n else k)
        for kk in (k-1,k,k+1):
            if 0<=kk<=n:
                key=(abs(n*num-kk*A),n,kk)
                if best is None or key<best: best=key
    _,n,k=best; g=gcd(k,n) if n else 1
    return (n//g,k//g) if g>1 else (n,k)

def simple_terms(d,N):
    A=1<<(N-1); n,k=best_nk_bound(d,N,256); base=A+(A*k)//n; e=d-base
    if e==0: return 0
    cur=base; t=0
    while e!=0 and t<200:
        Di=A//abs(e)
        if Di==0: break
        cur+=(1 if e>0 else -1)*(A//Di); e=d-cur; t+=1
    return t

def nested_terms(d,N,NMAX):
    """recursively best-approx the residual at each scale; count levels to 0."""
    r=d; b=N; t=0
    while t<400:
        if r==0: break
        ar=abs(r); s=1 if r>0 else -1
        b=ar.bit_length()
        if b<4: t+=1; break          # tiny residual = last term
        A=1<<(b-1)
        n,k=best_nk_bound(ar,b,NMAX)
        base=A+(A*k)//n
        newr=s*(ar-base)
        t+=1
        if newr==r: break            # no progress guard
        r=newr
    return t

def simple_gran_terms(d,N,g):
    """simple recursion but each term only removes ~g fewer bits (coarser)."""
    A=1<<(N-1); n,k=best_nk_bound(d,N,256); base=A+(A*k)//n; e=d-base
    cur=base; t=0
    while e!=0 and t<400:
        be=abs(e).bit_length()
        step=1<<max(be-g,0)               # coarse chunk ~ top g bits of the error
        cur+=(1 if e>0 else -1)*step; e=d-cur; t+=1
    return t

N=246; A=1<<(N-1); SAMPLE=400
ds=[A+rnd.randrange(A) for _ in range(SAMPLE)]
def dist(fn):
    dd={}
    for d in ds:
        t=fn(d); dd[t]=dd.get(t,0)+1
    return dict(sorted(dd.items()))
def mean(fn): return sum(fn(d) for d in ds)/SAMPLE

S=lambda d: simple_terms(d,N)
print(f"term-count distributions at N={N} ({SAMPLE} random keys):")
print(f"  (S) simple/CSV      mean={mean(S):.2f}  {dist(S)}")
print(f"  (N256) nested n<=256 mean={mean(lambda d:nested_terms(d,N,256)):.2f}  {dist(lambda d:nested_terms(d,N,256))}")
print(f"  (N2048) nested n<=2048 mean={mean(lambda d:nested_terms(d,N,2048)):.2f}  {dist(lambda d:nested_terms(d,N,2048))}")
print("  target from user: ~10-11 terms")
