"""v2/v3 were mis-built the same way TWICE: _frame.speeds() SORTS, so index k in v stopped
corresponding to residue pi[k].  Runner identity is now carried through the sort by tag.

u_i = pi(i) + 8 q_i.  Deformation splits into pi-part and q-part.
Question: is the isolation's neighbour a function of pi alone?
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
def build(pi,q):
    """Return (v, tag_at_position) with v a legal sorted arrangement in reduced units, or None."""
    u=[pi[k]+8*q[k] for k in range(8)]
    if len(set(u))!=8 or gcd_all(u)!=1: return None
    order=sorted(range(8), key=lambda k: u[k])
    v=speeds([u[k]-min(u)+1 for k in range(8)])
    return v, order          # order[p] = tag of the runner sitting at sorted position p

rng=random.Random(4004)
gs=gt=cs=ct=ctsame=0; trials=0
while trials<2000:
    pi=[rng.randrange(8) for _ in range(8)]
    A=build(pi,[rng.randrange(0,7) for _ in range(8)])
    B=build(pi,[rng.randrange(0,7) for _ in range(8)])
    if A is None or B is None: continue
    trials+=1
    (v,oA),(w,oB)=A,B
    posA={oA[p]:p for p in range(8)}; posB={oB[p]:p for p in range(8)}
    for tag in range(8):
        i,j0=posA[tag],posB[tag]
        a1,b1=nb(v,i,F(1,8)); a2,b2=nb(w,j0,F(1,8))
        gt+=1
        if ((pi[oA[a1]]-pi[tag])%8==(pi[oB[a2]]-pi[tag])%8 and
            (pi[oA[b1]]-pi[tag])%8==(pi[oB[b2]]-pi[tag])%8): gs+=1
        ds =sorted(F(abs(v[k]-v[i]))  for k in range(8) if k!=i)
        ds2=sorted(F(abs(w[k]-w[j0])) for k in range(8) if k!=j0)
        t,_=cascade(ds); t2,_=cascade(ds2)
        if t is None or t2 is None: continue
        ct+=1
        if t==t2: ctsame+=1
        A1,B1=nb(v,i,t); A2,B2=nb(w,j0,t2)
        if ((pi[oA[A1]]-pi[tag])%8==(pi[oB[A2]]-pi[tag])%8 and
            (pi[oA[B1]]-pi[tag])%8==(pi[oB[B2]]-pi[tag])%8): cs+=1
print(f"{trials} residue-matched pairs, reduced units (g = 1), identity carried by tag\n")
print(f"(a) GRID INSTANT t = 1/8 : neighbour residue-offsets unchanged by q-deformation")
print(f"      {gs} of {gt}   ({gs/gt:.6f})")
print(f"(b) CASCADE INSTANT      : instant unchanged   {ctsame} of {ct}  ({ctsame/ct:.4f})")
print(f"                           neighbour unchanged {cs} of {ct}  ({cs/ct:.4f})")
