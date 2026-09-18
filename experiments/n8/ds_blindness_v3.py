"""v2 used min()/max() over (distance, offset) tuples, which breaks TIES on the offset -- an
arbitrary choice that could manufacture the 41.9%.  Redone with tied subjects EXCLUDED, so every
counted subject has a strictly unique nearest-ahead and nearest-behind.

All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
from collections import defaultdict, Counter
def frac(x): return x-floor(x)
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
def nbr(v,i,g,p):
    """(ahead, behind) as signed offsets, or None if either is TIED."""
    t=F(p,8*g)
    rel=[(frac(F(v[j]-v[i])*t), ((v[j]-v[i])//g)%8) for j in range(8) if j!=i]
    ds_=[r for r,_ in rel]
    lo=min(ds_); hi=max(ds_)
    if ds_.count(lo)>1 or ds_.count(hi)>1: return None
    a=[o for r,o in rel if r==lo][0]; b=[o for r,o in rel if r==hi][0]
    return a,b
rng=random.Random(4242)
seen=defaultdict(list)
for _ in range(40000):
    v=speeds(rng.sample(range(1,40),8))
    g=gcd_all(v)
    for i in range(8):
        ds=tuple(sorted(abs(v[j]-v[i])//g for j in range(8) if j!=i))
        seen[ds].append((v,i,g))
rep=0; ord_multi=unord_multi=0; tied_dropped=0
for rows in seen.values():
    o=set(); u=set(); kept=0
    for v,i,g in rows:
        r=nbr(v,i,g,1)
        if r is None: tied_dropped+=1; continue
        kept+=1; a,b=r
        o.add((a,b)); u.add(tuple(sorted((min(a,8-a), min(b,8-b)))))
    if kept<2: continue
    rep+=1
    if len(o)>1: ord_multi+=1
    if len(u)>1: unord_multi+=1
print(f"  tied subjects dropped: {tied_dropped}")
print(f"  {rep} disparity multisets with >=2 UNTIED subjects\n")
print(f"  carry >1 ORDERED  (ahead,behind) offset pair : {ord_multi}   ({ord_multi/rep:.4f})")
print(f"  carry >1 UNORDERED |offset| pair            : {unord_multi}   ({unord_multi/rep:.4f})")
