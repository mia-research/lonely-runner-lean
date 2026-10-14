#!/usr/bin/env python3
"""THE GRID-NEIGHBOURHOOD CERTIFICATE (from the owner's transition map).

At t = a/8 + eps with r_j = e_j*a mod 8, runner j needs ||r_j/8 + e_j eps|| >= 1/8, whose
admissible set is a union of intervals of eps; the one containing 0 is
    [ (1-r_j)/(8 e_j) , (7-r_j)/(8 e_j) ].
Intersecting over j:   L(a) = max_j (1-r_j)/(8e_j),  U(a) = min_j (7-r_j)/(8e_j).
L(a) <= U(a)  =>  every eps in [L,U] is a witness.   PROVED, three lines.

Allowing runner j to use a NON-principal interval (index k_j) gives the wrapped version.
"""
from fractions import Fraction as F
from itertools import combinations, product
from functools import reduce
from math import gcd

def LU(E,a):
    L=max(F(1-(e*a)%8, 8*e) for e in E)
    U=min(F(7-(e*a)%8, 8*e) for e in E)
    return L,U
def cert(E):
    for a in (1,3,5,7):
        L,U=LU(E,a)
        if L<=U: return a,L,U
    return None
def cert_wrapped(E,K=1):
    """allow each runner an interval index in [-K,K]; try all combinations (cheap for K=1)"""
    for a in (1,3,5,7):
        ivs=[[ (F(1-(e*a)%8,8*e)+F(k,e), F(7-(e*a)%8,8*e)+F(k,e)) for k in range(-K,K+1)]
             for e in E]
        for combo in product(*ivs):
            L=max(x for x,_ in combo); U=min(y for _,y in combo)
            if L<=U: return a,L,U
    return None

print("CONTROL A -- the certificate must FIRE with L=U=0 on the three tight instances")
for E in ((1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13)):
    c=cert(E)
    print(f"  {E}: {c}   {'PASS (degenerate, t=a/8 exactly)' if c and c[1]==c[2]==0 else 'check'}")

print("\nCONTROL B -- every fired certificate must be a REAL witness (verified independently)")
def isw(E,t): return all(min((e*t)%1, 1-(e*t)%1)>=F(1,8) for e in E)
import random; random.seed(5)
n=0; bad=0
for _ in range(4000):
    E=tuple(sorted(random.sample(range(1,40),7)))
    if reduce(gcd,E)!=1: continue
    c=cert(E)
    if not c: continue
    a,L,U=c; n+=1
    for eps in {L,U,(L+U)/2}:
        if not isw(E, F(a,8)+eps): bad+=1
print(f"  {n} fired certificates, {bad} non-witnesses   {'PASS' if bad==0 else '*** FAIL ***'}")

print("\nCOVERAGE, exhaustive over [1..18]")
c1=c1h=0; c2=c2h=c2w=0; res=resh=resw=0
PHI={2:1,3:2,4:2,5:4,6:2,7:6,8:4}
for E in combinations(range(1,19),7):
    if reduce(gcd,E)!=1: continue
    h=cert(E) is not None
    if all(e%8 for e in E):
        c1+=1; c1h+=h
    else:
        c2+=1; c2h+=h
        w = h or (cert_wrapped(E) is not None)
        c2w+=w
        if sum(p for d,p in PHI.items() if all(e%d for e in E))==0:
            res+=1; resh+=h; resw+=w
print(f"  Case 1 ({c1}):        principal certificate fires {c1h} = {100*c1h/c1:.2f}%")
print(f"  Case 2 ({c2}):        principal {c2h} = {100*c2h/c2:.2f}%   wrapped(K=1) {c2w} = {100*c2w/c2:.2f}%")
print(f"  RESIDUAL ({res}):      principal {resh} = {100*resh/res:.2f}%   wrapped(K=1) {resw} = {100*resw/res:.2f}%")
print(f"\n  (the earlier uniform-window version of this idea reached 14.05% on Case 2)")
