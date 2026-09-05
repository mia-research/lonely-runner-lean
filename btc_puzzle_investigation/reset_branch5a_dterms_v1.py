#!/usr/bin/env python3
"""
BRANCH 5a: shared early continued-fraction (D-term) quotients -- the direct
creator-construction fingerprint, flagged un-run in the doc.

A random real's CF quotients follow Gauss-Kuzmin, P(a=k)=log2(1+1/(k(k+2))). A
constructed key (sum of a few unit fractions / a shared recipe) leaves SMALL and/or
SHARED early quotients. Object: u_N = Fraction(d_N - 2^(N-1), 2^(N-1)); take the first
CF quotients a1,a2,a3. Joint test (Method-2 maxT collision statistic) on a1, on (a1,a2),
and on a1's value distribution, vs the 100k matched null. Exact rationals only.
Control: keys with a forced shared a1 must fire.
"""
import csv, os, random
from fractions import Fraction
from collections import Counter, defaultdict
import numpy as np
from reset_common import load_solved

solved = load_solved()
KEYS = sorted(solved)
BITS = {N: solved[N]["bits"] for N in KEYS}

def cf_quotients(num, den, k=4):
    """first k CF quotients of num/den (0<=num<den)."""
    qs=[]
    for _ in range(k):
        if den==0: break
        a=num//den; qs.append(a)
        num, den = den, num - a*den
    return qs

def features(dmap):
    a1=[]; a12=[]
    for N in KEYS:
        A=1<<(BITS[N]-1)
        q=cf_quotients(dmap[N]-A, A, 5)     # [a0=0, a1, a2, a3, ...]
        q=(q+[0,0,0,0,0])
        a1.append(q[1]); a12.append((q[1],q[2]))   # skip the leading integer part 0
    return a1,a12

def coll(vals):
    c=Counter(vals); return sum(v*v for v in c.values())

# null pool
pool=defaultdict(list)
with open(os.path.join(os.path.dirname(__file__),
        "constructed_keys_1to160_100k_exact.csv")) as f:
    for r in csv.DictReader(f):
        pool[int(r["bits"])].append(int(r["d"]))
rng=random.Random(0x5DEA)
def null_map():
    return {N:(rng.choice(pool[BITS[N]]) if pool.get(BITS[N])
              else rng.randrange(1<<(BITS[N]-1),1<<BITS[N])) for N in KEYS}

print("=== BRANCH 5a: shared early CF (D-term) quotients ===\n")
B=6000
ref=[]
for _ in range(B):
    a1,a12=features(null_map())
    ref.append((coll(a1), coll(a12)))
ref=np.array(ref)
def z(obs,col):
    m,s=ref[:,col].mean(),ref[:,col].std() or 1.0; return (obs-m)/s

a1r,a12r=features({N:solved[N]["d"] for N in KEYS})
o1,o12=coll(a1r),coll(a12r)
p1=(np.sum(ref[:,0]>=o1)+1)/(B+1)
p12=(np.sum(ref[:,1]>=o12)+1)/(B+1)
print(f"a1 collision T={o1} (null mean {ref[:,0].mean():.1f}), z={z(o1,0):.2f}, p={p1:.4f}")
print(f"(a1,a2) collision T={o12} (null mean {ref[:,1].mean():.1f}), z={z(o12,1):.2f}, p={p12:.4f}")
print(f"observed a1 distribution: {dict(sorted(Counter(a1r).items())[:8])}")
# Gauss-Kuzmin expectation for a1=1,2,3
import math
gk={k: math.log2(1+1/(k*(k+2))) for k in (1,2,3,4)}
print(f"Gauss-Kuzmin P(a1=k): {{k:round(v,3) for k,v in gk.items()}}".replace("round(v,3)",""),
      {k:round(v,3) for k,v in gk.items()})

# control
def ctrl_map():
    out={}
    for N in KEYS:
        A=1<<(BITS[N]-1)
        # force a1=2 => u in (1/3,1/2): pick d-A near 0.4*A
        out[N]=A + (2*A)//5 + rng.randrange(0, max(1,A//50))
    return out
a1c,a12c=features(ctrl_map()); oc=coll(a1c)
pc=(np.sum(ref[:,0]>=oc)+1)/(B+1)
print(f"\n[CTRL forced a1] a1 collision T={oc}, p={pc:.4f} -> {'FIRES' if pc<0.01 else 'no'}")
print(f"   (control a1 dist: {dict(sorted(Counter(a1c).items())[:5])})")
print("\n-> " + ("SHARED early quotients: construction fingerprint" if min(p1,p12)<0.05
      else "no shared-early-quotient structure beyond the matched null (control-valid)"))
