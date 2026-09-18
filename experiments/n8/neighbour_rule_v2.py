"""Split the owner's question in two.

Any arrangement decomposes as  u_i = pi(i) + 8 q_i   (residue + whole laps).
Deformation therefore has TWO independent parts: moving pi, and moving q.

(a) At a GRID INSTANT t = p/(8g): is the neighbour a function of pi ALONE?
    If yes, q-deformation is INVISIBLE to the neighbour -- perfectly predictable (no change),
    and pi-deformation moves it by the +-p rule.
(b) At the CASCADE's instant (generally NOT a grid instant): same test.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
from collections import Counter
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def frac(x): return x-floor(x)
def reduced(v):
    g=0
    for a,b in combinations(v,2): g=gcd(g,abs(b-a))
    return [(x-min(v))//g for x in v], g
def nb(v,i,t):
    sep=[(frac(F(v[j]-v[i])*t), j) for j in range(8) if j!=i]
    return min(sep)[1], max(sep)[1]
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def cascade(ds):
    m=min(ds); t=TH/m; n=0
    while n<4000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return t,n
        t=max(nextOp(d,t) for d in b); n+=1
    return None,0

rng=random.Random(101)
grid_same=0; grid_tot=0; casc_same=0; casc_tot=0
casc_t_same=0
trials=0
while trials<1500:
    # base arrangement in REDUCED units: residues pi (a permutation is not required) + laps q
    pi=[rng.randrange(8) for _ in range(8)]
    q =[rng.randrange(0,6) for _ in range(8)]
    u =[pi[k]+8*q[k] for k in range(8)]
    if len(set(u))!=8: continue
    # q-deformation: same residues, different whole laps
    q2=[rng.randrange(0,6) for _ in range(8)]
    u2=[pi[k]+8*q2[k] for k in range(8)]
    if len(set(u2))!=8: continue
    try:
        v =speeds([x+1 for x in u])
        v2=speeds([x+1 for x in u2])
    except Exception: continue
    trials+=1
    _,g =reduced(v); _,g2=reduced(v2)
    for i in range(8):
        # (a) grid instant p=1
        a1,b1=nb(v,i,F(1,8*g)); a2,b2=nb(v2,i,F(1,8*g2))
        grid_tot+=1
        if (pi[a1]-pi[i])%8==(pi[a2]-pi[i])%8 and (pi[b1]-pi[i])%8==(pi[b2]-pi[i])%8: grid_same+=1
        # (b) cascade instant
        ds =sorted(F(abs(v[j]-v[i]))  for j in range(8) if j!=i)
        ds2=sorted(F(abs(v2[j]-v2[i])) for j in range(8) if j!=i)
        t,_=cascade(ds); t2,_=cascade(ds2)
        if t is None or t2 is None: continue
        casc_tot+=1
        if t*g==t2*g2: casc_t_same+=1
        A1,B1=nb(v,i,t); A2,B2=nb(v2,i,t2)
        if (pi[A1]-pi[i])%8==(pi[A2]-pi[i])%8 and (pi[B1]-pi[i])%8==(pi[B2]-pi[i])%8: casc_same+=1
print(f"{trials} residue-matched pairs\n")
print("(a) GRID INSTANT  -- neighbour residue-offsets unchanged by q-deformation:")
print(f"    {grid_same} of {grid_tot}   ({grid_same/grid_tot:.6f})")
print()
print("(b) CASCADE INSTANT -- same test:")
print(f"    instant itself (in lap units) unchanged : {casc_t_same} of {casc_tot}  ({casc_t_same/casc_tot:.4f})")
print(f"    neighbour residue-offsets unchanged     : {casc_same} of {casc_tot}  ({casc_same/casc_tot:.4f})")
