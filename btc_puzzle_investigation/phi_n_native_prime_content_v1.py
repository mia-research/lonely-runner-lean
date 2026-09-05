#!/usr/bin/env python3
"""
Where does the omega(n) lean live? Per-prime over/under-representation in the
factorisations of real-key denominators n vs matched Farey null. Ties to the
curve if small primes {2,3,7} (bad primes of y^2=x^3+7) or {3} (chi_-3) dominate.
Exact counts; null = uniform-d draws, same bands.
"""
import csv, random
from math import gcd
from fractions import Fraction
random.seed(20260710)
NMAX=256; NULL_DRAWS=3000; MIN_BITS=20
def factorize(m):
    f={}; d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d += 1 if d==2 else 2
    if m>1: f[m]=f.get(m,0)+1
    return f
def best_nk(d,N):
    A=1<<(N-1); num=d-A; best=None
    for n in range(1,NMAX+1):
        k=(2*n*num+A)//(2*A)
        if k<0:k=0
        if k>n:k=n
        for kk in (k-1,k,k+1):
            if 0<=kk<=n:
                key=(abs(n*num-kk*A),n,kk)
                if best is None or key<best: best=key
    _,n,k=best; g=gcd(k,n) if n else 1
    if g>1: n//=g; k//=g
    return n,k
rows=[]
with open("puzzles_verified.csv") as fh:
    for r in csv.DictReader(fh):
        N=int(r["bits"]); d=int(r["private_key"],16)
        if N>=MIN_BITS and r.get("onchain_pubkey_matches_our_X","Y")!="N":
            rows.append((N,d))
from collections import Counter
real=Counter(); nreal=0
null=Counter(); nnull=0
for (N,d) in rows:
    n,k=best_nk(d,N)
    if n>1:
        nreal+=1
        for p in factorize(n): real[p]+=1
    A=1<<(N-1); span=(1<<N)-A; draws=min(NULL_DRAWS,span)
    for _ in range(draws):
        nn,_=best_nk(A+random.randrange(span),N)
        if nn>1:
            nnull+=1
            for p in factorize(nn): null[p]+=1
def frac3(fr):
    fr=Fraction(fr); s=(fr.numerator*1000)//fr.denominator
    return f"{s//1000}.{s%1000:03d}"
print(f"real keys (n>1): {nreal};  null keys: {nnull}\n")
print(f"{'prime':>6s} {'real rate':>10s} {'null rate':>10s} {'ratio':>7s}")
for p in [2,3,5,7,11,13,17,19,23]:
    rr=Fraction(real[p],nreal); nn=Fraction(null[p],nnull) if nnull else Fraction(1)
    ratio=frac3(rr*Fraction(nn.denominator,nn.numerator)) if nn.numerator else "inf"
    print(f"{p:>6d} {frac3(rr):>10s} {frac3(nn):>10s} {ratio:>7s}")
# small-prime {2,3,7} (curve bad primes) share of real vs null factorisations
def share(cnt,tot,S): return Fraction(sum(cnt[p] for p in S), tot) if tot else Fraction(0)
for S,lab in [({2,3,7},"{2,3,7} bad primes"),({3},"{3} chi_-3"),({2,3,5,7},"{2,3,5,7}")]:
    print(f"\n{lab}: real={frac3(share(real,sum(real.values()),S))}  "
          f"null={frac3(share(null,sum(null.values()),S))}  (share of all prime-factor incidences)")
