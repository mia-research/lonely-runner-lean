r"""
ok_tightprox_v1 -- route (B): is "many relations" really "close to a tight instance"?

The three tight instances (TIGHT_INSTANCES_v1, reconfirmed by ok_ufull_v1) are
   T1 = {1,2,3,4,5,6,7}, T2 = {1,2,3,4,5,7,12}, T3 = {1,4,5,6,7,11,13},
each with int X = 0.  Case-2 tuples near them should inherit a small lonely set.

Eyeballing the hardest tuples suggests they share 5 or 6 speeds with a DILATE of a tight
instance:  (2,6,7,8,10,13,14) meets 2*T1 = {2,4,6,8,10,12,14} in {2,6,8,10,14}.
Measured here: overlap = max over tight instances T and dilations lambda of |E n lambda*T|,
against |G|.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd
from collections import defaultdict
import statistics

TIGHT=[(1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13)]
def arcs(e): return [(F(8*j+1,8*e), F(8*j+7,8*e)) for j in range(e)]
def inter(A,B):
    out=[]; i=j=0
    while i<len(A) and j<len(B):
        lo=max(A[i][0],B[j][0]); hi=min(A[i][1],B[j][1])
        if lo<hi: out.append((lo,hi))
        if A[i][1]<B[j][1]: i+=1
        else: j+=1
    return out
def G_measure(E):
    cur=arcs(E[0])
    for e in E[1:]:
        cur=inter(cur,arcs(e))
        if not cur: return F(0)
    return sum((b-a for a,b in cur), F(0))
def overlap(E, LMAX=30):
    S=set(E); best=0; arg=None
    for T in TIGHT:
        for lam in range(1,LMAX+1):
            o=len(S & {lam*x for x in T})
            if o>best: best=o; arg=(T,lam)
    return best,arg
def nrel(E):
    S=set(E); return sum(1 for x in E for y in E if x<y and x+y in S)

rows=[]
for E in combinations(range(1,25),7):
    if reduce(gcd,E)!=1: continue
    if not any(e%8==0 for e in E): continue
    rows.append((G_measure(list(E)),E))
rows.sort(key=lambda r:r[0])
print(f"{len(rows)} Case-2 tuples in [1..24].\n")
print(f"{'E':30} {'|G|':>10} {'rel':>4} {'overlap':>8}  with")
for g,E in rows[:10]:
    o,arg=overlap(E)
    print(f"{str(E):30} {float(g):10.6f} {nrel(E):>4} {o:>8}  {arg[1]}*{arg[0]}")
print()
buck=defaultdict(list)
for g,E in rows:
    o,_=overlap(E)
    buck[o].append(float(g))
print(f"{'overlap':>8} {'count':>8} {'min |G|':>11} {'mean |G|':>11}")
for o in sorted(buck):
    v=buck[o]
    print(f"{o:>8} {len(v):>8} {min(v):11.6f} {statistics.mean(v):11.6f}")
tgt=float(F(93,14560))
print(f"\ntarget = {tgt:.6f}")
for thr in (5,6):
    hi=[g for o,v in buck.items() if o>=thr for g in v]
    lo=[g for o,v in buck.items() if o<thr for g in v]
    print(f"  overlap >= {thr}: {len(hi):6} tuples, min |G| = {min(hi):.6f}")
    print(f"  overlap <  {thr}: {len(lo):6} tuples, min |G| = {min(lo):.6f}  "
          f"({min(lo)/tgt:.1f}x target)")
