#!/usr/bin/env python3
"""
Powered smoothness test on the LARGER puzzle keys, with rigor.
Primary (pre-registered): Omega_B(d) = # prime factors <=B (with multiplicity), B=10^4,
ALL small primes, on Group B (bit-length >=20). Real-82 vs bit-matched null from 100k.
Two-sided bootstrap p + effect size + 95% CI of the null mean.
Controls: exclude {2,5} (decimal confound); Group A (<20 bit, degenerate) for contrast;
B in {10^3,10^4,10^5}; distinct-prime count. Exact integer trial division; no float in
the feature. Bootstrap p = integer counts.
"""
import csv, random
from sympy import primerange
def omega_B(d, primes, drop=()):
    c=0
    for p in primes:
        if p in drop:
            while d%p==0: d//=p
            continue
        while d%p==0: d//=p; c+=1
    return c
PB={1000:list(primerange(2,1000)),10000:list(primerange(2,10000)),100000:list(primerange(2,100000))}

real=[];rbits=[]
with open('puzzles_verified.csv') as f:
    for row in csv.DictReader(f):
        real.append(int(row['private_key'],16));rbits.append(int(row['bits']))
synth={}
with open('constructed_keys_1to160_100k_exact.csv') as f:
    for row in csv.DictReader(f):
        synth.setdefault(int(row['bits']),[]).append(int(row['d']))

# precompute Omega for real and (lazily) synth per bit-length used
def groupidx(cond): return [i for i,b in enumerate(rbits) if cond(b)]
GA=groupidx(lambda b:b<20); GB=groupidx(lambda b:b>=20)
print(f"Group A (<20 bit, fixed/low-entropy): {len(GA)} keys;  Group B (>=20 bit): {len(GB)} keys")

rng=random.Random(20260712)
def test(idxs,B,drop=(),NBOOT=20000,name=""):
    primes=PB[B]
    ro=[omega_B(real[i],primes,drop) for i in idxs]
    realmean=sum(ro)/len(ro)
    # precompute synth Omega for the needed bit-lengths (cache)
    need={rbits[i] for i in idxs}
    cache={b:[omega_B(d,primes,drop) for d in synth[b]] for b in need}
    nulls=[]
    for _ in range(NBOOT):
        s=sum(rng.choice(cache[rbits[i]]) for i in idxs)/len(idxs)
        nulls.append(s)
    nulls.sort()
    nullmean=sum(nulls)/NBOOT
    above=sum(1 for x in nulls if x>=realmean); below=sum(1 for x in nulls if x<=realmean)
    p=2*min(above,below)/NBOOT
    lo=nulls[int(0.025*NBOOT)];hi=nulls[int(0.975*NBOOT)]
    print(f"  {name:30} real={realmean:.3f} null={nullmean:.3f} (95%[{lo:.3f},{hi:.3f}]) eff={realmean-nullmean:+.3f} p2={p:.4f}{'  <-' if p<0.05 else ''}")
    return p

print("\n=== PRIMARY (pre-registered): Omega_{10^4}, all small primes, Group B ===")
p_primary=test(GB,10000,name="B>=20, Omega<=1e4 (all)")

print("\n=== decimal confound control: exclude {2,5} ===")
test(GB,10000,drop=(2,5),name="B>=20, Omega<=1e4 (no 2,5)")
test(GB,10000,drop=(2,),name="B>=20, Omega<=1e4 (no 2)")

print("\n=== robustness: bound B in {1e3,1e5} ===")
test(GB,1000,name="B>=20, Omega<=1e3 (all)")
test(GB,100000,name="B>=20, Omega<=1e5 (all)")

print("\n=== contrast: Group A (<20 bit, degenerate null) ===")
test(GA,10000,name="A<20, Omega<=1e4 (all)")

print("\n=== also on ALL 82 (to reproduce the prior M1 p~0.058) ===")
test(list(range(82)),1000,name="all-82, Omega<=1e3 (all)")
print(f"\nPRIMARY p (Bonferroni x ~6 secondaries if reporting them): {p_primary:.4f} -> {min(1,p_primary*6):.4f}")
