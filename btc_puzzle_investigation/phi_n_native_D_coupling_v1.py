#!/usr/bin/env python3
"""
Propagation probe: does the residual D remember the prime factors of n?

The old work treated D as 'lower ~60% of free bits, structureless'. But it never
asked whether the FINE part (D) is coupled to the COARSE part's arithmetic (the
prime factorisation of n). That coupling is exactly a 'bidirectional propagation'
signature. Two exact tests, real keys vs matched Farey null:
  T1. gcd(D, n) > 1  rate.
  T2. D ≡ 0 (mod p) for at least one prime p | n  (n>1) rate.
  T3. corr(D_terms, omega(n)) sign, real vs null spread.
All exact integer / Fraction. D = d - base, base = A + floor(A*k/n).
"""
import csv, random
from math import gcd, comb
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
def omega(m): return 0 if m<=1 else len(factorize(m))
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
def D_terms_count(d,N,base):
    A=1<<(N-1); running=base; err=d-running; terms=0
    while err!=0 and terms<200:
        Di=A//abs(err)
        if Di==0: break
        running += (1 if err>0 else -1)*(A//Di)
        err=d-running; terms+=1
    return terms
def coupling(d,N):
    n,k=best_nk(d,N); A=1<<(N-1); base=A+(A*k)//n; D=d-base
    if n<=1:
        return dict(n=n,g=1,hit=0,omega=0,dt=0)
    primes=list(factorize(n).keys())
    g=gcd(abs(D),n)
    hit=1 if any(D%p==0 for p in primes) else 0
    return dict(n=n,g=1 if g>1 else 0,hit=hit,omega=omega(n),dt=D_terms_count(d,N,base))

rows=[]
with open("puzzles_verified.csv") as fh:
    for r in csv.DictReader(fh):
        N=int(r["bits"]); d=int(r["private_key"],16)
        if N>=MIN_BITS and r.get("onchain_pubkey_matches_our_X","Y")!="N":
            rows.append((N,d))

real={"g":[], "hit":[], "dt":[], "om":[]}
null={"g":[0,0], "hit":[0,0]}
null_corr_beats=0; null_corr_total=0
# collect (dt, omega) pairs real, and per-key null pairs for a paired corr-sign test
real_dt=[]; real_om=[]
null_dt_all=[]; null_om_all=[]
for (N,d) in rows:
    rf=coupling(d,N)
    real["g"].append(rf["g"]); real["hit"].append(rf["hit"])
    real_dt.append(rf["dt"]); real_om.append(rf["omega"])
    A=1<<(N-1); span=(1<<N)-A; draws=min(NULL_DRAWS,span)
    for _ in range(draws):
        nb=coupling(A+random.randrange(span),N)
        null["g"][1]+=1; null["g"][0]+=nb["g"]
        null["hit"][1]+=1; null["hit"][0]+=nb["hit"]
        null_dt_all.append(nb["dt"]); null_om_all.append(nb["omega"])

def frac3(fr):
    fr=Fraction(fr); s=(fr.numerator*1000)//fr.denominator
    return f"{s//1000}.{s%1000:03d}"
def binom_two_sided(hi,total):
    if total==0: return Fraction(1)
    k=min(hi,total-hi)
    return min(Fraction(2*sum(comb(total,i) for i in range(k+1)),1<<total),Fraction(1))

print(f"solved keys (N>={MIN_BITS}): {len(rows)}\n")
print("PROPAGATION: does residual D remember n's prime factors?  (real vs null rate)")
for key,lab in [("g","gcd(D,n)>1"),("hit","D=0 mod some p|n")]:
    rr=Fraction(sum(real[key]),len(real[key]))
    nn=Fraction(null[key][0],null[key][1])
    print(f"  {lab:22s} real={frac3(rr)} ({sum(real[key])}/{len(real[key])})   null={frac3(nn)}")

# corr sign: covariance sign of (dt, omega), exact via sum of centered products*denoms
def cov_sign(xs,ys):
    m=len(xs); sx=sum(xs); sy=sum(ys)
    # sign of  m*sum(xy) - sx*sy   (exact integer)
    v=m*sum(x*y for x,y in zip(xs,ys)) - sx*sy
    return (v>0)-(v<0)
rs=cov_sign(real_dt,real_om)
# null: block the null pairs into pseudo-samples of size len(rows), get cov-sign distribution
import itertools
blk=len(rows); pos=0; signs=[]
while pos+blk<=len(null_dt_all):
    signs.append(cov_sign(null_dt_all[pos:pos+blk], null_om_all[pos:pos+blk])); pos+=blk
pos_frac=Fraction(sum(1 for s in signs if s>0),len(signs)) if signs else Fraction(0)
print(f"\nCOUPLING corr(D_terms, omega(n)): real cov-sign={rs:+d};  "
      f"null blocks with +sign: {frac3(pos_frac)} of {len(signs)}")
print(f"  real (D_terms, omega) means: dt={frac3(Fraction(sum(real_dt),len(real_dt)))}, "
      f"omega={frac3(Fraction(sum(real_om),len(real_om)))}")
