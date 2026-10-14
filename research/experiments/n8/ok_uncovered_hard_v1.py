r"""
ok_uncovered_hard_v1 -- how hard are the shapes outside the three proved leaves?

Framework criterion (STATUS section 0): a witness exists iff  S \ union B_m  is non-empty,
   S     = { x : uncovered(E_non, x) non-empty }        (non-divisible runners)
   B_m   = { x : 8m blocks everything }                 (divisible runner e = 8m)
because a divisible runner has e*r = 0 mod 8, so it blocks every r exactly on B_m.
The union bound closes a tuple when |S| > |union B_m|.  Exact rationals, ENTRY evaluation.
"""
from itertools import combinations
from functools import reduce
from math import gcd
from fractions import Fraction as F
from collections import defaultdict
import random, sys

UNITS = {1,3,5,7}
def bad(e,t): return frozenset(r for r in range(8) if (e*r+t)%8 in (0,7))
def cells(S):
    pts={F(0),F(1)}
    for e in S:
        for j in range(1,e+1):
            q=F(j,e)
            if 0<q<1: pts.add(q)
    p=sorted(pts); return list(zip(p,p[1:]))
def fl(e,a): v=e*a; return v.numerator//v.denominator

def measures(E):
    res=[e%8 for e in E]
    Ediv=[e for e,r in zip(E,res) if r==0]; Enon=[e for e,r in zip(E,res) if r!=0]
    Smeas=F(0); Bmeas=F(0); Wmeas=F(0)
    for a,b in cells(list(E)):
        w=b-a
        cov=set()
        for e in Enon: cov|=bad(e,fl(e,a))
        inS = len(cov)<8
        inB = any(len(bad(e,fl(e,a)))==8 for e in Ediv)
        if inS: Smeas+=w
        if inB: Bmeas+=w
        if inS and not inB: Wmeas+=w
    return Smeas,Bmeas,Wmeas

def shape(E):
    res=[e%8 for e in E]
    Ediv=[e for e,r in zip(E,res) if r==0]; Rnon={r for r in res if r!=0}
    if not Ediv: return "L1"
    uc=UNITS<=Rnon
    if not uc and len(Rnon)==5: return "DU5"
    if uc and len(Rnon)==5 and len(Ediv)==2: return "UC5_div2"
    if uc and len(Rnon)==5 and len(Ediv)==1: return "UC5_div1"
    return f"{'UC' if uc else 'DU'} |R|={len(Rnon)} |Ediv|={len(Ediv)}"

LIM=int(sys.argv[1]) if len(sys.argv)>1 else 26
SAMP=int(sys.argv[2]) if len(sys.argv)>2 else 60
buckets=defaultdict(list)
for E in combinations(range(1,LIM+1),7):
    if reduce(gcd,E)!=1: continue
    s=shape(E)
    if s.startswith(("L1","DU5","UC5")): continue
    buckets[s].append(E)

random.seed(11)
print(f"{'uncovered shape':26} {'n':>7} {'min |S|':>10} {'max|UB|':>9} {'min margin |S|-|UB|':>20} {'min witness':>12} {'fails':>6}")
for s in sorted(buckets, key=lambda k:-len(buckets[k])):
    pop=buckets[s]; samp=random.sample(pop,min(SAMP,len(pop)))
    rows=[measures(E)+(E,) for E in samp]
    minS=min(r[0] for r in rows); maxB=max(r[1] for r in rows)
    marg=min(r[0]-r[1] for r in rows); minW=min(r[2] for r in rows)
    fails=sum(1 for r in rows if r[0]<=r[1])
    print(f"{s:26} {len(pop):7} {float(minS):10.5f} {float(maxB):9.5f} "
          f"{float(marg):20.5f} {float(minW):12.5f} {fails:6}")
print("\n'fails' = sampled tuples where the union bound |S| > |UB| does NOT close.")
print("'min witness' = min measure of S \\ UB; 0 would mean NO witness exists (LRC(8) false).")
