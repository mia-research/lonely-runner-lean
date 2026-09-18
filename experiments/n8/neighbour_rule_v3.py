"""v2 was mis-built: residues must be taken in REDUCED units (gcd of pairwise differences = 1).
Here both members of every pair are forced to reduce to themselves, so pi really is the residue.

u_i = pi(i) + 8 q_i.  q-deformation keeps pi, changes the whole-lap parts only.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def frac(x): return x-floor(x)
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
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

rng=random.Random(2027)
gs=gt=cs=ct=ctsame=0; trials=0
while trials<1500:
    pi=[rng.randrange(8) for _ in range(8)]
    q =[rng.randrange(0,7) for _ in range(8)]
    q2=[rng.randrange(0,7) for _ in range(8)]
    u =[pi[k]+8*q[k]  for k in range(8)]
    u2=[pi[k]+8*q2[k] for k in range(8)]
    if len(set(u))!=8 or len(set(u2))!=8: continue
    if gcd_all(u)!=1 or gcd_all(u2)!=1: continue      # <- the fix: reduced units, g = 1
    v =speeds([x-min(u)+1  for x in u])
    v2=speeds([x-min(u2)+1 for x in u2])
    # residues of the REDUCED arrangement (min subtracted shifts every residue equally,
    # so residue DIFFERENCES -- the only thing the rule uses -- are unchanged)
    trials+=1
    for i in range(8):
        a1,b1=nb(v,i,F(1,8)); a2,b2=nb(v2,i,F(1,8))
        gt+=1
        if (pi[a1]-pi[i])%8==(pi[a2]-pi[i])%8 and (pi[b1]-pi[i])%8==(pi[b2]-pi[i])%8: gs+=1
        ds =sorted(F(abs(v[j]-v[i]))   for j in range(8) if j!=i)
        ds2=sorted(F(abs(v2[j]-v2[i])) for j in range(8) if j!=i)
        t,_=cascade(ds); t2,_=cascade(ds2)
        if t is None or t2 is None: continue
        ct+=1
        if t==t2: ctsame+=1
        A1,B1=nb(v,i,t); A2,B2=nb(v2,i,t2)
        if (pi[A1]-pi[i])%8==(pi[A2]-pi[i])%8 and (pi[B1]-pi[i])%8==(pi[B2]-pi[i])%8: cs+=1
print(f"{trials} residue-matched pairs, both in reduced units (g = 1)\n")
print(f"(a) GRID INSTANT t = 1/8 : neighbour residue-offsets unchanged by q-deformation")
print(f"      {gs} of {gt}   ({gs/gt:.6f})")
print(f"(b) CASCADE INSTANT      : instant unchanged   {ctsame} of {ct}  ({ctsame/ct:.4f})")
print(f"                           neighbour unchanged {cs} of {ct}  ({cs/ct:.4f})")
