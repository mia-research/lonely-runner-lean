#!/usr/bin/env python3
"""The crowding dichotomy with the 8 removed -- stated and checked for general n.

n runners: stationary at 0 plus n-1 distinct primitive speeds E. At t = a/n + eps with
r_j = e_j a mod n, runner j needs ||r_j/n + e_j eps|| >= 1/n, whose interval containing 0 is
    [ (1-r_j)/(n e_j), (n-1-r_j)/(n e_j) ].
L(a) = max_j (...), U(a) = min_j (...); L <= U gives a witness.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd

def LU(E,a,n):
    return (max(F(1-(e*a)%n, n*e) for e in E), min(F(n-1-(e*a)%n, n*e) for e in E))
def units(n): return [a for a in range(1,n) if gcd(a,n)==1]
def isw(E,t,n): return all(min((F(e)*t)%1, 1-(F(e)*t)%1) >= F(1,n) for e in E)

for n,hi in ((4,26),(5,22),(6,18),(7,16)):
    U_=units(n); tot=c1=c2=c3=c4=0
    for E in combinations(range(1,hi+1),n-1):
        if reduce(gcd,E)!=1: continue
        tot+=1
        # CLAIM 1: no crowding (bijection) => L=U=0
        for a in U_:
            R=[(e*a)%n for e in E]
            if sorted(R)==list(range(1,n)):
                L,Uu=LU(E,a,n)
                if not (L==0 and Uu==0): c1+=1
        # CLAIM 2: some e = 0 mod n => a vacancy in {1..n-1} at every a
        if any(e%n==0 for e in E):
            for a in U_:
                if len(set((e*a)%n for e in E) & set(range(1,n)))==n-1: c2+=1
        # CLAIM 3: exists a with residue n-1 vacant  <=>  occupied units != all units
        can = any((n-1) not in [(e*a)%n for e in E] for a in U_)
        full = set(u for u in U_ if u in {e%n for e in E}) == set(U_)
        if can == full: c3+=1
        # CONTROL: every fired certificate is a real witness
        for a in U_:
            L,Uu=LU(E,a,n)
            if L<=Uu:
                for eps in {L,Uu,(L+Uu)/2}:
                    if not isw(E, F(a,n)+eps, n): c4+=1
                break
    print(f"n={n}, speeds [1..{hi}], {tot} primitive tuples:")
    print(f"   Claim1 (bijection => L=U=0) failures {c1}   Claim2 (vacancy) failures {c2}"
          f"   Claim3 (steerable <=> not unit-complete) failures {c3}")
    print(f"   CONTROL fired-certificate-is-a-witness failures {c4}   "
          f"{'ALL PASS' if c1==c2==c3==c4==0 else '*** FAIL ***'}")
