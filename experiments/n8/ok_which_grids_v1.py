#!/usr/bin/env python3
"""WHICH GRIDS ACHIEVE GLOBAL ISOLATION -- criterion, verification, and the
permutation + deviation decomposition."""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd

def criterion(V):
    n=len(V); w=[v-V[0] for v in V]; g=reduce(gcd,[abs(x) for x in w if x]) or 1
    return sorted((x//g)%n for x in w)==list(range(n))
def brute(V):
    """exact: global isolation forces all gaps = 1/n, so t = p/(n*g); check those"""
    n=len(V); w=[v-V[0] for v in V]; g=reduce(gcd,[abs(x) for x in w if x]) or 1
    for p in range(1,n*g+1):
        if gcd(p,n*g)!=1: continue
        t=F(p,n*g); P=sorted({F(v)*t%1 for v in V})
        if len(P)<n: continue
        gp=min(min(P[i+1]-P[i] for i in range(n-1)),1-P[-1]+P[0])
        if gp>=F(1,n): return True
    return False

print("CRITERION vs exact check, all n-subsets of [1..N]:")
for n,N in ((4,16),(5,15),(6,14),(7,14)):
    bad=tot=hit=0
    for V in combinations(range(1,N+1),n):
        tot+=1; c=criterion(V)
        if c: hit+=1
        if c!=brute(V): bad+=1
    print(f"  n={n}, [1..{N}]: {tot:>6} sets, {hit:>5} achieve global isolation "
          f"({100*hit/tot:5.2f}%)   criterion disagreements: {bad}")
print()
print("THE RULE.  Translate so one runner is 0, divide by the gcd of the differences.")
print("Global isolation  <=>  the reduced speeds are a COMPLETE residue system mod n,")
print("and it then happens at exactly phi(n) times, t = p/(n*g), gcd(p,n)=1.")
print()
print("PERMUTATION + DEVIATION.  Write each reduced speed as  u_i = pi(i) + n*q_i,")
print("pi(i) = u_i mod n.  Then pi alone decides it and the q_i are FREE:")
base=(0,1,2,3,4,5,6,7)
import random; random.seed(0)
for trial in range(5):
    q=[random.randint(0,6) for _ in range(8)]
    V=tuple(sorted(base[i]+8*q[i] for i in range(8)))
    if len(set(V))<8: continue
    print(f"   pi = identity, q = {q}  ->  V = {V}   global isolation: {criterion(V)}")
print()
print("and a NON-permutation pi cannot be rescued by any q:")
bad=(0,0,2,2,5,6,6,7)   # the residues of (0,2,6,7,8,10,13,14)
for trial in range(4):
    q=[random.randint(0,9) for _ in range(8)]
    V=sorted(bad[i]+8*q[i] for i in range(8))
    if len(set(V))<8: continue
    print(f"   pi = {bad}, q = {q}  ->  V = {tuple(V)}   global isolation: {criterion(tuple(V))}")
