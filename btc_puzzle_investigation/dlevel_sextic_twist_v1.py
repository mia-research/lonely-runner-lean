#!/usr/bin/env python3
"""
Sextic-character / twist test (the one curve-native note left untested).
X-coordinate is in the CSV, so chi6(X) = X^((p-1)/6) mod p is cheap (no scalar
mult).  The 6 sextic classes = the 6 sextic twists' natural partition on j=0.
Q1: is chi6(X) uniform over the real keys, or biased toward a twist?
Q2: do the same-n coupled groups SHARE a sextic class more than chance?
Exact; permutation p-values integer-decided.
"""
import csv, random
from collections import Counter
from math import gcd
from knd_common import best_nk

P=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
assert (P-1)%6==0
EXP=(P-1)//6
# label the 6 sextic classes by discrete index: chi6 in <g> of order 6.
# use a fixed sextic nonresidue base to map the 6 values -> {0..5} by powers.
def sextic_val(x): return pow(x%P,EXP,P)
# build value->index map from a generator of the order-6 subgroup
g=2
while True:
    r=sextic_val(g)
    orbit=[pow(r,i,P) for i in range(6)]
    if len(set(orbit))==6: break
    g+=1
idx={orbit[i]:i for i in range(6)}
def chi6_idx(x): return idx[sextic_val(x)]

rows=[]
with open("btc_puzzle_master_exact.csv") as fh:
    for r in csv.DictReader(fh):
        if r["status"]!="SOLVED": continue
        rows.append((int(r["puzzle"]),int(r["bits"]),int(r["priv_dec"]),int(r["X_hex"],16)))
rows.sort()

cls={}; dist=Counter()
for p,N,d,X in rows:
    c=chi6_idx(X); cls[p]=c
    if N>=20: dist[c]+=1
print("Q1: chi6(X) class distribution over solved keys (N>=20):")
print("   ", dict(sorted(dist.items())), f" (uniform ~ {sum(dist.values())/6:.1f} each)")
tot=sum(dist.values()); exp=tot/6
chi2=sum((dist.get(c,0)-exp)**2/exp for c in range(6))
print(f"    chi^2={chi2:.2f} df=5  (5.35=median; >11.07 => p<0.05)")

# Q2: same-n groups sharing sextic class
groups={}
for p,N,d,X in rows:
    n,k=best_nk(d,N); groups.setdefault(n,[]).append(p)
multi={n:ps for n,ps in groups.items() if len(ps)>=2 and n>=20}
print("\nQ2: sextic class within same-n coupled groups:")
obs_share=0; obs_pairs=0
for n,ps in multi.items():
    cs=[cls[p] for p in ps]
    print(f"   n={n} puzzles={ps} chi6={cs}")
    for i in range(len(ps)):
        for j in range(i+1,len(ps)):
            obs_pairs+=1
            if cls[ps[i]]==cls[ps[j]]: obs_share+=1
# null: shuffle class labels among the N>=20 keys, recount shared pairs within groups
keys20=[p for p,N,_,_ in rows]          # sextic class is bit-independent: use all
labels=[cls[p] for p in keys20]
pos={p:i for i,p in enumerate(keys20)}
random.seed(20260711); R=200000; ge=0
grouplists=[[pos[p] for p in ps] for ps in multi.values()]
for _ in range(R):
    random.shuffle(labels)
    s=0
    for gl in grouplists:
        for i in range(len(gl)):
            for j in range(i+1,len(gl)):
                if labels[gl[i]]==labels[gl[j]]: s+=1
    if s>=obs_share: ge+=1
print(f"\n   shared-class pairs within groups: observed={obs_share}/{obs_pairs}  "
      f"null>=obs: {ge}/{R} (~{(1000*ge)//R}e-3)")
