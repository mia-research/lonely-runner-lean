#!/usr/bin/env python3
"""
v2: tighten the phi(n)-native (n,k,D) probe on the 82 solved keys.
Adds over v1:
  - EXACT two-sided binomial sign-test p-values (integer comb()).
  - matched-null baseline rates for pm1 (k=+-1 mod n) and ord(k)<=2.
  - n-MAGNITUDE as a control feature: if real keys DON'T lean to large n but DO
    lean to high omega(n), the omega signal is intrinsic, not a big-n artifact.
All exact. Null = matched uniform-d draws in the same bit-band, same decomposition.
"""
import csv, random
from math import gcd, comb
from fractions import Fraction

random.seed(20260710)
NMAX = 256; NULL_DRAWS = 4000; MIN_BITS = 20

def factorize(m):
    f={}; d=2
    while d*d<=m:
        while m%d==0: f[d]=f.get(d,0)+1; m//=d
        d += 1 if d==2 else 2
    if m>1: f[m]=f.get(m,0)+1
    return f
def omega(m): return 0 if m<=1 else len(factorize(m))
def mobius(m):
    if m==1: return 1
    f=factorize(m)
    return 0 if any(e>1 for e in f.values()) else (-1 if len(f)%2 else 1)
def euler_phi(m):
    if m<=1: return 1
    r=m
    for p in factorize(m): r-=r//p
    return r
def mult_order(a,n):
    a%=n
    if n<=2 or gcd(a,n)!=1: return None
    o,x=1,a%n
    while x!=1:
        x=(x*a)%n; o+=1
        if o>n: return None
    return o
def best_nk(d,N):
    A=1<<(N-1); num=d-A; best=None
    for n in range(1,NMAX+1):
        k=(2*n*num+A)//(2*A)
        if k<0: k=0
        if k>n: k=n
        for kk in (k-1,k,k+1):
            if 0<=kk<=n:
                key=(abs(n*num-kk*A),n,kk)
                if best is None or key<best: best=key
    _,n,k=best; g=gcd(k,n) if n else 1
    if g>1: n//=g; k//=g
    return n,k
def feats(d,N):
    n,k=best_nk(d,N)
    ordk=mult_order(k,n)
    return dict(n=n,k=k,omega=omega(n),sqfree=1 if mobius(n)!=0 else 0,
                phi_ratio=Fraction(euler_phi(n),n) if n else Fraction(1),
                pm1=1 if (n>2 and (k%n) in (1,n-1)) else 0,
                ord_le2=None if ordk is None else (1 if ordk<=2 else 0))

def binom_two_sided(hi,total):
    """exact two-sided p for hi successes out of total, p0=1/2 (integer comb)."""
    if total==0: return Fraction(1)
    k=min(hi,total-hi)
    tail=sum(comb(total,i) for i in range(0,k+1))
    p=Fraction(2*tail,1<<total)
    return min(p,Fraction(1))

rows=[]
with open("puzzles_verified.csv") as fh:
    for r in csv.DictReader(fh):
        N=int(r["bits"]); d=int(r["private_key"],16)
        if N>=MIN_BITS and r.get("onchain_pubkey_matches_our_X","Y")!="N":
            rows.append((N,d))
print(f"solved keys (N>={MIN_BITS}): {len(rows)}\n")

num_feats=["omega","phi_ratio","n"]          # ranked features (n = control)
bin_feats=["sqfree","pm1","ord_le2"]         # binary: compare real rate to null rate
ranks={f:[] for f in num_feats}
real_bin={f:[] for f in bin_feats}
null_bin={f:[0,0] for f in bin_feats}        # [hits, total]

for (N,d) in rows:
    rf=feats(d,N); A=1<<(N-1); span=(1<<N)-A
    draws=min(NULL_DRAWS,span)
    nulls=[feats(A+random.randrange(span),N) for _ in range(draws)]
    for f in num_feats:
        rv=rf[f]
        lt=sum(1 for nb in nulls if nb[f]<rv); eq=sum(1 for nb in nulls if nb[f]==rv)
        ranks[f].append(Fraction(2*lt+eq,2*len(nulls)))
    for f in bin_feats:
        if rf[f] is not None:
            real_bin[f].append(rf[f])
        for nb in nulls:
            if nb[f] is not None:
                null_bin[f][1]+=1; null_bin[f][0]+=nb[f]

def frac3(fr):
    fr=Fraction(fr); s=(fr.numerator*1000)//fr.denominator
    return f"{s//1000}.{s%1000:03d}"

print("RANKED features — real key vs matched Farey null (0.5=no bias):")
print(f"{'feature':12s} {'mean-rank':>9s} {'hi/lo':>8s} {'sign-test p':>12s}")
for f in num_feats:
    rl=ranks[f]; m=len(rl)
    mean=sum(rl)*Fraction(1,m)
    hi=sum(1 for r in rl if r>Fraction(1,2)); lo=sum(1 for r in rl if r<Fraction(1,2))
    p=binom_two_sided(max(hi,lo),hi+lo)
    print(f"{f:12s} {frac3(mean):>9s} {f'{hi}/{lo}':>8s} {frac3(p):>12s}")

print("\nBINARY features — real rate vs null rate:")
print(f"{'feature':12s} {'real':>12s} {'null':>10s}")
for f in bin_feats:
    rb=real_bin[f]; rr=Fraction(sum(rb),len(rb)) if rb else Fraction(0)
    nn=Fraction(null_bin[f][0],null_bin[f][1]) if null_bin[f][1] else Fraction(0)
    print(f"{f:12s} {f'{sum(rb)}/{len(rb)}={frac3(rr)}':>12s} {frac3(nn):>10s}")

print("\nREAD: 'n' rank ~0.5 + 'omega' rank >0.5  =>  omega excess is intrinsic,")
print("      not a big-n artifact.  'phi_ratio' <0.5 is the same lean (low phi/n).")
