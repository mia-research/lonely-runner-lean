#!/usr/bin/env python3
"""PREREG_GCD_CLASS_INVARIANCE_v1, retargeted onto the RIGHT object.

GECT v5.0's Dual phi(n) Law says collapse structure at n is determined by gcd(r,n)
alone -- graded there "empirically validated for n=12, requires extended testing".
Translated to our object, the hypothesis is

  H (R0): u(E) depends only on the multiset { gcd(e,8) : e in E }.
  R1:     u(E) depends only on the multiset { e mod 8 : e in E }.

R1 is the rung that would matter: finitely many classes for UNBOUNDED speeds, hence a
candidate finite bound table for u(E) < 1, which U_REFORMULATION_v2 §1 proves is the
whole of n=8 outside Case 1.

NOTE ON TARGET.  An earlier framing tested u(E_non) (CASE_TREE_AUDIT_v1's recommendation
#1).  U_REFORMULATION_v2 §2 proves that target dead -- the E_non/E_div split is lossy at
every |E_div|.  This script therefore runs on the FULL tuple, divisible runners kept in.

Exact Fraction.  Second implementation (bitmask) cross-checked against the oracle.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd
import random, sys

# ---- oracle: verbatim from ok_umax_v1.py ----
def bad(e,t): return frozenset(r for r in range(8) if (e*r+t)%8 in (0,7))
def cells(S):
    pts={F(0),F(1)}
    for e in S:
        for j in range(1,e+1):
            q=F(j,e)
            if 0<q<1: pts.add(q)
    p=sorted(pts); return list(zip(p,p[1:]))
def fl(e,a): v=e*a; return v.numerator//v.denominator
def u_oracle(E):
    tot=F(0)
    for a,b in cells(E):
        cov=set()
        for e in E: cov|=bad(e,fl(e,a))
        if len(cov)==8: tot+=b-a
    return tot

# ---- C3: independent implementation, 8-bit masks, bad[] keyed on (e mod 8, t) ----
BAD={}
for r8 in range(8):
    for t in range(8):
        m=0
        for r in range(8):
            if (r8*r+t)%8 in (0,7): m|=1<<r
        BAD[(r8,t)]=m
def u_mask(E):
    tot=F(0)
    for a,b in cells(E):
        m=0
        for e in E: m|=BAD[(e%8, fl(e,a)%8)]
        if m==255: tot+=b-a
    return tot

def kappa(E):  return tuple(sorted(gcd(e,8) for e in E))
def res8(E):   return tuple(sorted(e%8 for e in E))

print("="*78)
print("P1 -- planted control: the three published argmaxes of U_REFORMULATION_v2 §2")
for E,want in (((1,4,12,20),F(1,3)), ((1,3,4,5,7),F(9,14)), ((1,4,5,6,7,11),F(125,154))):
    got=u_oracle(E); ok = got==want
    print(f"  u{E} = {got}   expected {want}   {'PASS' if ok else '*** FAIL ***'}")
    if not ok: sys.exit("P1 failed -- run void")

print("\nC3 -- second implementation vs oracle, census k=1..4 from [1..14]")
pool=[e for e in range(1,15)]
n=0; bad3=0
for k in range(1,5):
    for E in combinations(pool,k):
        if u_oracle(E)!=u_mask(E): bad3+=1
        n+=1
print(f"  {n} sets, mismatches {bad3}   {'PASS' if bad3==0 else '*** FAIL ***'}")
if bad3: sys.exit("C3 failed -- run void")

print("\nC2 / C8 -- dilation.  docstring of ok_umax_v1.py claims u(lambda E) = u(E)")
random.seed(20260911)
sets=[tuple(sorted(random.sample(range(1,13),k))) for k in (3,4,5) for _ in range(40)]
for lab,lams in (("ODD  lambda",(3,5,7,9)), ("EVEN lambda",(2,4,6))):
    mism=[(E,l,u_oracle(E),u_oracle(tuple(l*e for e in E))) for E in sets for l in lams
          if u_oracle(E)!=u_oracle(tuple(l*e for e in E))]
    print(f"  {lab}: {len(mism)} mismatches of {len(sets)*len(lams)}"
          f"   {'invariant' if not mism else 'NOT invariant'}")
    if mism: print(f"    first: u{mism[0][0]}={mism[0][2]}  vs  u({mism[0][1]}E)={mism[0][3]}")

print("\n" + "="*78)
print("R0 / R1 -- falsification search.  ONE unequal pair in a class is a proof.")
for k in (3,4,5):
    tabK, tabR = {}, {}
    pool=[e for e in range(1,21)]
    for E in combinations(pool,k):
        uu=u_oracle(E)
        tabK.setdefault(kappa(E),{}).setdefault(uu,[]).append(E)
        tabR.setdefault(res8(E),{}).setdefault(uu,[]).append(E)
    for lab,tab in (("R0 gcd-multiset",tabK), ("R1 mod-8 multiset",tabR)):
        live={c:d for c,d in tab.items() if not (len(d)==1 and F(0) in d)}
        viol={c:d for c,d in live.items() if len(d)>=2}
        print(f"  k={k}  {lab:20s}: {len(tab):4d} classes, {len(live):4d} live,"
              f" {len(viol):4d} with >=2 distinct u  -> H {'REJECTED' if viol else 'no counterexample'}")
        if viol:
            c=sorted(viol, key=lambda c:(len(viol[c]),c))[0]; d=viol[c]
            vs=sorted(d); a1=d[vs[0]][0]; a2=d[vs[-1]][0]
            print(f"        minimal witness  class {c}:  u{a1} = {vs[0]}   vs   u{a2} = {vs[-1]}")

print("\n" + "="*78)
print("IMPACT OF THE PRIMITIVITY FILTER on U_REFORMULATION_v2 §2's quoted maxima.")
print("ok_umax_v1.py:62,73 skip imprimitive E.  Since u is NOT even-dilation invariant,")
print("those sets were never evaluated.  Max over ALL E_non vs max over PRIMITIVE only:")
pool=[e for e in range(1,21) if e%8]
for k,quoted in ((4,F(1,3)),(5,F(9,14)),(6,F(125,154))):
    bp=bi=F(0); ap=ai=None
    for E in combinations(pool,k):
        uu=u_oracle(E)
        prim = reduce(gcd,E)==1
        if prim:
            if uu>bp: bp,ap=uu,E
        else:
            if uu>bi: bi,ai=uu,E
    allb,alla = (bp,ap) if bp>=bi else (bi,ai)
    print(f"  k={k}: primitive max {bp} at {ap}  (quoted {quoted}, {'matches' if bp==quoted else 'DIFFERS'})")
    print(f"        imprimitive max {bi} at {ai}   ->  overall max {allb} at {alla}")
