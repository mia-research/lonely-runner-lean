#!/usr/bin/env python3
"""
Vector 3: local components of the keys at the conductor primes (84)=(2^2)(3)(7).
For each key d compute nu_q(d) (q-adic valuation) and residues at the conductor
moduli, compare the 82 real keys to a bit-length-matched null from the 100k pool.
Discriminate: conductor primes {2,3,7} vs decimal primes {2,5} vs controls {11,13}.
If {3,7} (conductor, non-decimal) show the same bias as 2, that is a conductor/CM
imprint; if only {2,5} show it, it is decimal. Exact ints; permutation p-values.
"""
import csv, random
from collections import Counter
def vq(d,q):
    c=0
    while d%q==0: d//=q; c+=1
    return c
real=[]; rbits=[]
with open('puzzles_verified.csv') as f:
    for row in csv.DictReader(f):
        real.append(int(row['private_key'],16)); rbits.append(int(row['bits']))
synth={}
with open('constructed_keys_1to160_100k_exact.csv') as f:
    for row in csv.DictReader(f):
        synth.setdefault(int(row['bits']),[]).append(int(row['d']))
rng=random.Random(20260712)
def bitmatched():
    return [rng.choice(synth[b]) for b in rbits if b in synth]

primes=[2,3,5,7,11,13]
label={2:'2 cond+dec',3:'3 CONDUCTOR',5:'5 decimal',7:'7 CONDUCTOR',11:'11 ctrl',13:'13 ctrl'}
print(f"{len(real)} real keys vs bit-matched null (100k). mean nu_q(d), two-sided perm p:")
realv={q:[vq(d,q) for d in real] for q in primes}
obs={q:sum(realv[q])/len(realv[q]) for q in primes}
NULL=20000
above={q:0 for q in primes}; below={q:0 for q in primes}
nullmean={q:0.0 for q in primes}
for _ in range(NULL):
    dr=bitmatched()
    for q in primes:
        m=sum(vq(d,q) for d in dr)/len(dr); nullmean[q]+=m
        if m>=obs[q]: above[q]+=1
        if m<=obs[q]: below[q]+=1
print(f"{'prime':14}{'real mean':>10}{'null mean':>10}{'p(2sided)':>11}")
for q in primes:
    p=2*min(above[q],below[q])/NULL
    print(f"{label[q]:14}{obs[q]:>10.3f}{nullmean[q]/NULL:>10.3f}{p:>11.4f}{'  <-' if p<0.05 else ''}")

# residues at conductor moduli 4,3,7 (the exact conductor (2^2)(3)(7)) vs null
print("\nresidue distributions at conductor moduli (real vs null dispersion, perm p):")
def disp(vals,m):
    c=Counter(v%m for v in vals); return sum((m*c[i]-len(vals))**2 for i in range(m))
for m in [4,3,7,84]:
    o=disp(real,m); worse=0
    for _ in range(NULL):
        if disp(bitmatched(),m)>=o: worse+=1
    print(f"  d mod {m:2d}: dispersion perm p={worse/NULL:.4f}{'  <-' if worse/NULL<0.05 else ''}")
