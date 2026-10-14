"""Matched null for neighbour_rule_v4's cascade figure.

v4 measured: pair two arrangements with the SAME residues pi, different whole laps q.  How often
do the neighbour residue-offsets agree?  Grid instant 16000/16000; cascade instant 10.4%.

10.4% means nothing without a null.  Here the same statistic is measured on pairs whose residues
are UNRELATED, so any agreement is coincidence.  All speeds positive."""
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
def build(rng,pi):
    q=[rng.randrange(0,7) for _ in range(8)]
    u=[pi[k]+8*q[k] for k in range(8)]
    if len(set(u))!=8 or gcd_all(u)!=1: return None
    order=sorted(range(8), key=lambda k: u[k])
    return speeds([u[k]-min(u)+1 for k in range(8)]), order

def run(rng, matched, N=2000):
    gs=gt=cs=ct=0; trials=0
    while trials<N:
        piA=[rng.randrange(8) for _ in range(8)]
        piB=piA if matched else [rng.randrange(8) for _ in range(8)]
        A=build(rng,piA); B=build(rng,piB)
        if A is None or B is None: continue
        trials+=1
        (v,oA),(w,oB)=A,B
        posA={oA[p]:p for p in range(8)}; posB={oB[p]:p for p in range(8)}
        for tag in range(8):
            i,j0=posA[tag],posB[tag]
            a1,b1=nb(v,i,F(1,8)); a2,b2=nb(w,j0,F(1,8))
            gt+=1
            if ((piA[oA[a1]]-piA[tag])%8==(piB[oB[a2]]-piB[tag])%8 and
                (piA[oA[b1]]-piA[tag])%8==(piB[oB[b2]]-piB[tag])%8): gs+=1
            ds =sorted(F(abs(v[k]-v[i]))  for k in range(8) if k!=i)
            ds2=sorted(F(abs(w[k]-w[j0])) for k in range(8) if k!=j0)
            t,_=cascade(ds); t2,_=cascade(ds2)
            if t is None or t2 is None: continue
            ct+=1
            if ((piA[oA[A1:=nb(v,i,t)[0]]]-piA[tag])%8==(piB[oB[A2:=nb(w,j0,t2)[0]]]-piB[tag])%8 and
                (piA[oA[nb(v,i,t)[1]]]-piA[tag])%8==(piB[oB[nb(w,j0,t2)[1]]]-piB[tag])%8): cs+=1
    return gs/gt, cs/ct, gt, ct

g1,c1,gt,ct=run(random.Random(4004), True)
g0,c0,_,_  =run(random.Random(9119), False)
print(f"                              grid instant    cascade instant")
print(f"  MATCHED (same residues)     {g1:.4f}          {c1:.4f}")
print(f"  NULL    (unrelated)         {g0:.4f}          {c0:.4f}")
print(f"  n = {gt} subject-pairs (grid), {ct} (cascade)")
