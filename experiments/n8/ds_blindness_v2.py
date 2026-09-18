"""Sharpen v1.  ds = multiset of |w_j - w_i|, so it determines each offset UP TO SIGN.
The neighbour ahead is at offset +p and behind at -p, so orientation is exactly what ds discards.

Question: is the UNORDERED neighbour pair ds-determined, leaving only orientation blind?  Or is
even the unordered pair not a function of ds?  The answer decides how strong the blindness claim
may be stated.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
from collections import defaultdict
def frac(x): return x-floor(x)
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
def nbr_offsets(v,i,g,p):
    """(ahead, behind) as SIGNED residue offsets, and the unordered pair of |offset|."""
    t=F(p,8*g)
    rel=[(frac(F(v[j]-v[i])*t), ((v[j]-v[i])//g)%8) for j in range(8) if j!=i]
    a=min(rel)[1]; b=max(rel)[1]
    return (a,b), tuple(sorted((min(a,8-a), min(b,8-b))))
rng=random.Random(4242)
seen=defaultdict(list)
for _ in range(40000):
    v=speeds(rng.sample(range(1,40),8))
    g=gcd_all(v)
    for i in range(8):
        ds=tuple(sorted(abs(v[j]-v[i])//g for j in range(8) if j!=i))
        seen[ds].append((v,i,g))
rep=[r for r in seen.values() if len(r)>1]
ord_multi=unord_multi=0
for rows in rep:
    o=set(); u=set()
    for v,i,g in rows:
        a,b=nbr_offsets(v,i,g,1); o.add(a); u.add(b)
    if len(o)>1: ord_multi+=1
    if len(u)>1: unord_multi+=1
print(f"  {len(rep)} disparity multisets seen more than once\n")
print(f"  carry >1 ORDERED   (ahead,behind) offset pair : {ord_multi}   ({ord_multi/len(rep):.4f})")
print(f"  carry >1 UNORDERED |offset| pair             : {unord_multi}   ({unord_multi/len(rep):.4f})")
print()
if unord_multi==0:
    print("  => ds fixes WHICH TWO runners bind; it loses only WHICH IS AHEAD.")
    print("     The blindness is exactly orientation -- a weaker claim than v1 stated.")
else:
    print("  => ds does not even fix which two runners bind.")
