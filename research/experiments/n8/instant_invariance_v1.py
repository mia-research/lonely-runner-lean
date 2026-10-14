"""Owner: "the possible intersection only comes up when looking at the NEIGHBOURS' interaction,
not the isolation."

Precise form of the claim: the multiplier group acts on the grid instants, and a quantity can
detect that action only if it VARIES across them.  So classify the framework's objects by
invariance over the phi(8) = 4 grid instants p = 1,3,5,7.

  invariant  -> blind to the group.  BS could never have surfaced from it.
  varying    -> resolves the group.  This is where the intersection appeared.

All speeds positive.  Exhaustive over the four instants; sampled over arrangements."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
from collections import Counter
def frac(x): return x-floor(x)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
def probe(v,i,g):
    """Every quantity, at each of the four grid instants."""
    out=[]
    for p in (1,3,5,7):
        t=F(p,8*g)
        rel=[(frac(F(v[j]-v[i])*t), j) for j in range(8) if j!=i]
        dist=sorted(circd(F(v[j]-v[i])*t) for j in range(8) if j!=i)
        out.append(dict(
            verdict = all(d>=F(1,8) for d in dist),
            slotset = tuple(sorted(r for r,_ in rel)),
            neighbours = (min(rel)[1], max(rel)[1]),
            mindist = min(dist),
            distmultiset = tuple(dist),
        ))
    return out
def invariance(rows,key):
    return len({r[key] for r in rows})==1

rng=random.Random(606)
keys=['verdict','distmultiset','slotset','mindist','neighbours']
grid=Counter(); gen=Counter(); ng=nn=0
while ng<800 or nn<800:
    v=speeds(rng.sample(range(1,60),8))
    g=gcd_all(v)
    u=[(x-min(v))//g for x in v]
    isgrid = len({x%8 for x in u})==8
    for i in range(8):
        rows=probe(v,i,g)
        tgt,cnt=(grid,'g') if isgrid else (gen,'n')
        if cnt=='g' and ng>=800: continue
        if cnt=='n' and nn>=800: continue
        for k in keys:
            if invariance(rows,k): tgt[k]+=1
        tgt['N']+=1
    ng=grid['N']; nn=gen['N']
print("  fraction of subjects for which the quantity is CONSTANT across all four grid instants\n")
print(f"  {'quantity':<16}  {'grids':>8}   {'general arrangements':>22}")
for k in keys:
    print(f"  {k:<16}  {grid[k]/grid['N']:>8.4f}   {gen[k]/gen['N']:>22.4f}")
print(f"\n  n = {grid['N']} grid subjects, {gen['N']} general subjects")
