#!/usr/bin/env python3
"""
v2: control the D<->n propagation test for the omega(n) confound.

For each real key with denominator n, the EXACT baseline probability that a
uniform residual D hits some prime p|n is  p_hit(n) = 1 - prod_{p|n}(1 - 1/p).
Summing p_hit over the real keys' OWN n gives the expected hit count E under
'D independent of n given n'. If observed hits ~ E, the earlier 0.396-vs-0.30 gap
was just the omega(n) difference (confound), NOT genuine coupling. If observed
>> E, the residual really does remember n's primes beyond chance. Exact Fractions.
"""
import csv
from math import gcd
from fractions import Fraction

NMAX=256; MIN_BITS=20
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

obs=0; E=Fraction(0); m=0
obs_g=0; E_g=Fraction(0)
for (N,d) in rows:
    n,k=best_nk(d,N)
    if n<=1: continue
    A=1<<(N-1); base=A+(A*k)//n; D=d-base
    primes=list(factorize(n).keys())
    m+=1
    # T2: hit some p|n
    hit=1 if any(D%p==0 for p in primes) else 0
    p_hit=Fraction(1)-Fraction(1)
    prod=Fraction(1)
    for p in primes: prod*= (1-Fraction(1,p))
    p_hit=1-prod
    obs+=hit; E+=p_hit
    # T1: gcd(D,n)>1  == hit some p|n as well for squarefree part; same baseline p_hit
    g=1 if gcd(abs(D),n)>1 else 0
    obs_g+=g; E_g+=p_hit

def frac3(fr):
    fr=Fraction(fr); s=(fr.numerator*1000)//fr.denominator
    return f"{s//1000}.{s%1000:03d}"

print(f"real keys (n>1, N>={MIN_BITS}): {m}\n")
print("omega-CONTROLLED propagation test (baseline uses each key's OWN n):")
print(f"  T2  D=0 mod some p|n : observed={obs}/{m}={frac3(Fraction(obs,m))}   "
      f"expected(E)={frac3(E)} hits = rate {frac3(E*Fraction(1,m))}")
print(f"  T1  gcd(D,n)>1       : observed={obs_g}/{m}={frac3(Fraction(obs_g,m))}   "
      f"expected(E)={frac3(E_g)} hits = rate {frac3(E_g*Fraction(1,m))}")
# rough z on Poisson-binomial (variance = sum p(1-p))
var=Fraction(0)
for (N,d) in rows:
    n,k=best_nk(d,N)
    if n<=1: continue
    prod=Fraction(1)
    for p in factorize(n): prod*=(1-Fraction(1,p))
    ph=1-prod; var+=ph*(1-ph)
# z as exact-ish: (obs-E)/sqrt(var)  -- sqrt only for display, integer core is obs-E vs var
from math import isqrt
num=obs-E
sv=isqrt(int(var))  # display only
print(f"\n  observed-expected = {frac3(num)} hits;  sqrt(variance) ≈ {sv};  "
      f"(obs-E)/sd ≈ {frac3(num*Fraction(1,max(sv,1)))}")
print("  READ: obs≈E  => earlier gap was the omega(n) confound (no extra coupling).")
print("        obs>>E => D genuinely remembers n's primes beyond chance.")
