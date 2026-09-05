#!/usr/bin/env python3
"""
Collision-graph v2 -- rigorous follow-ups to the p=0.0015 consecutive-n signal.
(1) max consecutive-run-length null (is the 58/59/60 length-3 run beyond Farey?)
(2) key-doubling / nesting check: is the n=129 run just u preserved by d~2*d?
    (if so it's a scaling artifact, not a denominator coupling)
(3) k-structure summary within the run.
Exact signal path (best_nk, Fraction); integer resample p-values.
"""
import csv, random
from fractions import Fraction
from math import gcd
from collections import Counter
from knd_common import best_nk

MASTER="btc_puzzle_master_exact.csv"; R=200000; SEED=20260711

solved=[]
with open(MASTER) as fh:
    for r in csv.DictReader(fh):
        if r["status"]!="SOLVED": continue
        solved.append((int(r["puzzle"]),int(r["bits"]),int(r["priv_dec"])))
solved.sort()
D={p:d for p,_,d in solved}
nk={p:best_nk(d,N) for p,N,d in solved}
ps=sorted(nk)

# ---- (1) max consecutive-run-length, matched Farey null -------------------
def max_run(nvec, pvec):
    best=1; cur=1
    for i in range(1,len(pvec)):
        if pvec[i]==pvec[i-1]+1 and nvec[i]==nvec[i-1]: cur+=1
        else: cur=1
        best=max(best,cur)
    return best

sub=[(p,N) for (p,N,_) in solved if N>=20]
pvec=[p for p,_ in sub]; nvec=[nk[p][0] for p,_ in sub]
obs_run=max_run(nvec,pvec)

random.seed(SEED)
pools={}
for _,N in sub:
    if N in pools: continue
    lo,hi=1<<(N-1),1<<N
    ds=range(lo,hi) if hi-lo<=4000 else (random.randrange(lo,hi) for _ in range(4000))
    pools[N]=[best_nk(d,N)[0] for d in ds]
ge=0
for _ in range(R):
    sim=[random.choice(pools[N]) for _,N in sub]
    if max_run(sim,pvec)>=obs_run: ge+=1
print(f"(1) max consecutive-run-length (N>=20): observed={obs_run}  "
      f"p(null>=obs)={ge}/{R} (~{(1000*ge)//R}e-3)")

# ---- (2) key-doubling / nesting check for the 129 run ---------------------
print("\n(2) is the n=129 run a doubling artifact?  (u preserved <=> d~2*d)")
for a,b in ((58,59),(59,60)):
    da,db=D[a],D[b]
    # exact positions u = d / 2^bits  (Fraction, interpretation only)
    ua=Fraction(da,1<<a); ub=Fraction(db,1<<b)
    # if doubling: db ~ 2*da ; compare exactly
    ratio=Fraction(db,da)
    du=ub-ua
    print(f"  #{a}->#{b}: d ratio db/da={float(ratio):.6f} (doubling=>~2.0)  "
          f"u: {float(ua):.6f}->{float(ub):.6f}  Δu={float(du):+.6f}")
# same-(n,k)? if u were preserved, k would be equal too:
ks=[nk[p][1] for p in (58,59,60)]
print(f"  k across run = {ks}  -> distinct k => u NOT preserved => not a doubling artifact")

# ---- (3) k-structure inside every shared-n group --------------------------
print("\n(3) k-structure within shared-n groups (any low-complexity pattern?)")
groups={}
for p,N,d in solved:
    n,k=nk[p]; groups.setdefault(n,[]).append((p,k))
for n in sorted(groups):
    g=groups[n]
    if len(g)<2 or n<20: continue           # skip trivial low-n
    ks=[k for _,k in g]; ps_=[p for p,_ in g]
    diffs=sorted(set(abs(a-b) for i,a in enumerate(ks) for b in ks[i+1:]))
    print(f"  n={n:4d} puzzles={ps_} k={ks}  pairwise|Δk|={diffs}  "
          f"gcd(all k,n)={gcd(gcd(*ks) if len(ks)>1 else ks[0], n)}")
