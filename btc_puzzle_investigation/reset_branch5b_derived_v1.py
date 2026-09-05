#!/usr/bin/env python3
"""
BRANCH 5b: run the validated joint-clustering instrument (Method 2 maxT) on DERIVED
objects it never saw -- the fixed-decomposition k and n values (the objects behind the
retracted base-10 finding). Null = 100k decomposed the SAME way (limit_denominator,
fixed NMAX). maxT over moduli; control must fire. Exact rationals only.
"""
import csv, os, random
from fractions import Fraction
from collections import Counter
import numpy as np
from reset_common import load_solved

NMAX=1024
solved=load_solved(); KEYS=sorted(solved); BITS={N:solved[N]["bits"] for N in KEYS}
def decomp(d,N):
    A=1<<(N-1); fr=Fraction(d-A,A).limit_denominator(NMAX)
    return fr.numerator, fr.denominator          # k, n

MODULI=list(range(2,201))+[256,512,1024,10,100,1000]
MODULI=sorted(set(MODULI)); M=len(MODULI)
def Tvec(vals):
    out=np.empty(M,dtype=np.int64)
    for j,m in enumerate(MODULI):
        c=Counter(v%m for v in vals); out[j]=sum(x*x for x in c.values())
    return out

# null pool of constructed keys, decomposed the same way (cache by bits)
raw=[]
with open(os.path.join(os.path.dirname(__file__),"constructed_keys_1to160_100k_exact.csv")) as f:
    for r in csv.DictReader(f):
        raw.append((int(r["bits"]),int(r["d"])))
from collections import defaultdict
pool=defaultdict(list)
for b,d in raw: pool[b].append(d)
rng=random.Random(0x5B)
def null_kn():
    ks=[]; ns=[]
    for N in KEYS:
        p=pool.get(BITS[N]); d=rng.choice(p) if p else rng.randrange(1<<(BITS[N]-1),1<<BITS[N])
        k,n=decomp(d,N); ks.append(k); ns.append(n)
    return ks,ns

print("=== BRANCH 5b: joint clustering on derived k and n (fixed decomp NMAX=%d) ===\n"%NMAX)
NR=3000
refK=[]; refN=[]
for _ in range(NR):
    ks,ns=null_kn(); refK.append(Tvec(ks)); refN.append(Tvec(ns))
refK=np.stack(refK); refN=np.stack(refN)
def maxz(T,ref):
    mu=ref.mean(0); sd=ref.std(0); sd[sd==0]=1; z=(T-mu)/sd; j=int(z.argmax()); return z.max(),MODULI[j]
# calibration
calK=[maxz(Tvec(null_kn()[0]),refK)[0] for _ in range(1500)]
calN=[maxz(Tvec(null_kn()[1]),refN)[0] for _ in range(1500)]

kr=[decomp(solved[N]["d"],N)[0] for N in KEYS]
nr=[decomp(solved[N]["d"],N)[1] for N in KEYS]
zk,mk=maxz(Tvec(kr),refK); pk=(sum(1 for x in calK if x>=zk)+1)/(len(calK)+1)
zn,mn=maxz(Tvec(nr),refN); pn=(sum(1 for x in calN if x>=zn)+1)/(len(calN)+1)
print(f"k-values : maxZ={zk:.2f} @ m={mk}; corrected p={pk:.4f}")
print(f"n-values : maxZ={zn:.2f} @ m={mn}; corrected p={pn:.4f}")

# control: clustered k
def ctrl_k(): return [ (7*((v//7)) ) for v in kr]  # force multiples of 7
zc,mc=maxz(Tvec(ctrl_k()),refK); pc=(sum(1 for x in calK if x>=zc)+1)/(len(calK)+1)
print(f"\n[CTRL k mult-of-7] maxZ={zc:.2f} @ m={mc}; p={pc:.4f} -> {'FIRES' if pc<0.01 else 'weak'}")
print("\n-> " + ("clustering in derived object" if min(pk,pn)<0.05
      else "no joint clustering in derived k or n values (control-valid)"))
