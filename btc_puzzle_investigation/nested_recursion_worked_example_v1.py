#!/usr/bin/env python3
"""
WORKED EXAMPLE of the nested (simple-fraction / remainder) recursion, to lock the
definition. At each level:
  - the current |value| v sits in [2^{b-1}, 2^b); its position is u=(v-2^{b-1})/2^{b-1}
  - approximate u by a SIMPLE FRACTION k/n (small denominator n<=NMAX)   <-- "near simple fraction"
  - subtract that fraction's value; the signed REMAINDER becomes the next level's value
  - recurse until the remainder is tiny.
Reconstruction (sum of the fraction-values, with signs) must equal d exactly.
Shows term count GROWING with bit-length. NMAX shown for two bounds (256 vs 2048).
"""
from math import gcd
import random
rnd=random.Random(11)

def best_nk_bound(v,b,NMAX):
    A=1<<(b-1); num=v-A; best=None
    for n in range(1,NMAX+1):
        k=(2*n*num+A)//(2*A); k=0 if k<0 else (n if k>n else k)
        for kk in (k-1,k,k+1):
            if 0<=kk<=n:
                key=(abs(n*num-kk*A),n,kk)
                if best is None or key<best: best=key
    _,n,k=best; g=gcd(k,n) if n else 1
    return (n//g,k//g) if g>1 else (n,k)

def nested(d,N,NMAX,show=False):
    r=d; terms=[]; recon=0; sign=1
    while r!=0 and len(terms)<80:
        ar=abs(r); s=1 if r>0 else -1; b=ar.bit_length()
        if b<4:
            terms.append(("tail",0,0,r)); recon+=r; break
        A=1<<(b-1)
        n,k=best_nk_bound(ar,b,NMAX)
        base=A+(A*k)//n
        recon += s*base
        newr=s*(ar-base)
        terms.append((b,n,k,newr))
        if show:
            print(f"    L{len(terms)-1}: |r|~2^{b}  ≈ simple fraction {k}/{n}  "
                  f"(value {s}·base, base≈2^{base.bit_length()})  -> remainder {'+' if newr>=0 else '-'}2^{abs(newr).bit_length() if newr else 0}")
        if newr==r: break
        r=newr
    return terms,recon

print("WORKED nested decomposition (NMAX=256), term count vs bit-length:")
for N in (48,96,160,246):
    A=1<<(N-1); d=A+rnd.randrange(A)
    terms,recon=nested(d,N,256,show=(N in (48,246)))
    ok = "EXACT" if recon==d else f"MISMATCH(recon-d={recon-d})"
    print(f"  N={N:>3}: {len(terms)} terms   reconstruction={ok}")
    if N in (48,246): print()

print("term-count vs denominator bound (mean over 200 keys, N=246):")
A=1<<245; ds=[A+rnd.randrange(A) for _ in range(200)]
for NMAX in (256,1024,2048,4096):
    m=sum(len(nested(d,246,NMAX)[0]) for d in ds)/200
    print(f"  NMAX={NMAX:>4}: mean {m:.1f} terms")
