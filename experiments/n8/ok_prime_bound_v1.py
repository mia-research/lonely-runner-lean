#!/usr/bin/env python3
"""Is dmin bounded in terms of q(E) = smallest prime dividing NO e_j?

DENOMINATOR_TOWER_v1 §6 leaves this untested. Candidates, in increasing weakness:
  H1  dmin <= q
  H2  dmin <= 2q
  H3  dmin <= p2  (second prime dividing no e_j)
Exact arithmetic; adversaries included, since random sampling was what broke last time.
"""
from math import gcd, lcm
from functools import reduce
from itertools import combinations
import random
from collections import Counter

def ok(E,d,a): return all(min((e*a)%d, d-(e*a)%d)*8 >= d for e in E)
def dmin(E,cap=6000):
    for d in range(2,cap+1):
        for a in range(1,d):
            if gcd(a,d)==1 and ok(E,d,a): return d
    return None
def primes(lim):
    s=[True]*(lim+1); s[0]=s[1]=False
    for i in range(2,int(lim**.5)+1):
        if s[i]:
            for j in range(i*i,lim+1,i): s[j]=False
    return [i for i,v in enumerate(s) if v]
P=primes(200000)
def freeprimes(E,k=3):
    out=[]
    for p in P:
        if all(e%p for e in E):
            out.append(p)
            if len(out)==k: return out
    return out

def report(name, tuples):
    worst1=worst2=worst3=(0,None); n=0
    for E in tuples:
        d=dmin(E)
        if d is None: continue
        fp=freeprimes(E)
        q=fp[0]; p2=fp[1] if len(fp)>1 else None
        n+=1
        if d-q>worst1[0]: worst1=(d-q,E,d,q)
        if d/q>worst2[0]: worst2=(d/q,E,d,q)
        if p2 and d-p2>worst3[0]: worst3=(d-p2,E,d,p2)
    print(f"\n{name}  ({n} tuples)")
    print(f"  H1 dmin<=q  : max(dmin-q)  = {worst1[0]:>6}   {'HOLDS' if worst1[0]<=0 else 'FAILS'}"
          f"   at {worst1[1]} dmin={worst1[2]} q={worst1[3]}")
    print(f"  H2 dmin<=2q : max(dmin/q)  = {worst2[0]:>6.3f}  {'HOLDS' if worst2[0]<=2 else 'FAILS'}"
          f"   at {worst2[1]} dmin={worst2[2]} q={worst2[3]}")
    print(f"  H3 dmin<=p2 : max(dmin-p2) = {worst3[0]:>6}   {'HOLDS' if worst3[0]<=0 else 'FAILS'}"
          f"   at {worst3[1]} dmin={worst3[2]} p2={worst3[3]}")

random.seed(20260911)
# A: complete Case-2 residual in [1..18]
PHI={2:1,3:2,4:2,5:4,6:2,7:6,8:4}
resid=[E for E in combinations(range(1,19),7)
       if reduce(gcd,E)==1 and any(e%8==0 for e in E)
       and sum(p for d,p in PHI.items() if all(e%d for e in E))==0]
report("A. complete Case-2 residual, [1..18]", resid)

# B: lcm adversaries -- the family that broke the universal bound
adv=[]
for D in range(6,40):
    L=reduce(lcm,range(1,D+1))
    for tail in ((1,2,3,5,7,11),(1,2,3,4,5,7),(2,3,5,7,11,13),(1,3,5,9,11,13)):
        E=tuple(sorted(set(tail+(L,))))
        if len(E)==7: adv.append(E)
report("B. lcm(1..D) adversaries, D=6..39", adv)

# C: SMOOTH adversaries -- speeds chosen to use up every small prime, maximising q
sm=[]
for _ in range(4000):
    ps=random.sample([2,3,5,7,11,13,17,19,23,29,31],6)
    E=sorted(set([p**random.randint(1,4) for p in ps]+[random.choice([6,12,24,30,42,60,120,210,840])]))
    if len(E)!=7: continue
    g=reduce(gcd,E); E=tuple(sorted(e//g for e in E))
    if len(set(E))==7: sm.append(E)
report("C. smooth adversaries (maximise q)", sm[:1500])

# D: large random, residual only
rnd=[]
while len(rnd)<4000:
    E=tuple(sorted(random.sample(range(1,3000),7)))
    g=reduce(gcd,E); E=tuple(e//g for e in E)
    if not any(e%8==0 for e in E): continue
    if sum(p for d,p in PHI.items() if all(e%d for e in E))!=0: continue
    rnd.append(E)
report("D. random residual, [1..3000]", rnd)
