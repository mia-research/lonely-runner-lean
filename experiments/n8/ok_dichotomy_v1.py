#!/usr/bin/env python3
"""THE CROWDING DICHOTOMY (owner's framing), made exact.

At t = a/8 the runners occupy residues r_j = e_j a mod 8; 8 sites, 7 runners + the
stationary one at 0.
  (i)  NO CROWDING: {r_j} is a bijection onto {1..7}  -- the AP pattern. Site 0 free,
       residues 1 and 7 both occupied, L = U = 0: witness with ZERO slack (tight).
  (ii) CROWDING: two runners share a residue => some residue in {1..7} is VACANT = room.
In Case 2 a multiple of 8 sits on 0 at every a, so a vacancy in {1..7} always exists.
Steering it: mult-by-a permutes the units transitively, so 7 can be vacated iff the
occupied odd set S is a PROPER subset of {1,3,5,7} -- iff NOT Unit-Complete.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd

def occ(E,a): return [ (e*a)%8 for e in E ]
def LU(E,a):
    return (max(F(1-(e*a)%8,8*e) for e in E), min(F(7-(e*a)%8,8*e) for e in E))
def UC(E): return {1,3,5,7} <= {e%8 for e in E}

print("CLAIM 1  no crowding at a  <=>  {r_j} is a bijection onto {1..7}  =>  L=U=0 (tight)")
bad=0; n=0
for E in combinations(range(1,19),7):
    if reduce(gcd,E)!=1: continue
    for a in (1,3,5,7):
        R=occ(E,a)
        if sorted(R)==list(range(1,8)):
            n+=1
            L,U=LU(E,a)
            if not (L==0 and U==0): bad+=1
print(f"  {n} (tuple,a) pairs with the AP pattern; L=U=0 fails in {bad}  "
      f"{'PASS' if bad==0 else '*** FAIL ***'}")

print("\nCLAIM 2  Case 2  =>  at least one residue of {1..7} is vacant, at every a")
bad=0; n=0
for E in combinations(range(1,19),7):
    if reduce(gcd,E)!=1 or all(e%8 for e in E): continue
    for a in (1,3,5,7):
        n+=1
        if len(set(occ(E,a)) & set(range(1,8)))==7: bad+=1
print(f"  {n} (Case-2 tuple, a) pairs; no vacancy in {bad}   {'PASS' if bad==0 else '*** FAIL ***'}")

print("\nCLAIM 3  exists a with residue 7 VACANT  <=>  NOT Unit-Complete")
bad=0; n=0
for E in combinations(range(1,19),7):
    if reduce(gcd,E)!=1: continue
    n+=1
    can = any(7 not in occ(E,a) for a in (1,3,5,7))
    if can == UC(E): bad+=1
print(f"  {n} primitive 7-tuples; equivalence fails in {bad}   "
      f"{'PASS -- EXACT' if bad==0 else '*** FAIL ***'}")

print("\nCLAIM 4  once 7 is vacated, the certificate fires iff a SPEED condition holds:")
print("         e_j <= (7 - r_j) * e0   for all j,  e0 = smallest multiple of 8 in E")
bad=0; n=0; fires=0
for E in combinations(range(1,19),7):
    if reduce(gcd,E)!=1 or all(e%8 for e in E) or UC(E): continue
    a=next(a for a in (1,3,5,7) if 7 not in occ(E,a))
    e0=min(e for e in E if e%8==0)
    R=occ(E,a)
    cond = all(e <= (7-r)*e0 for e,r in zip(E,R) if r!=0)
    L,U=LU(E,a); n+=1
    if (L<=U)!=cond: bad+=1
    fires+=cond
print(f"  {n} non-Unit-Complete Case-2 tuples; speed condition <=> L<=U fails in {bad}  "
      f"{'PASS -- EXACT' if bad==0 else '*** FAIL ***'}")
print(f"  and it holds for {fires} of them = {100*fires/n:.2f}%")

print("\nSUMMARY OF THE DICHOTOMY, exhaustive over [1..18]")
tot=c1=uc=nuc=0
for E in combinations(range(1,19),7):
    if reduce(gcd,E)!=1: continue
    tot+=1
    if all(e%8 for e in E): c1+=1
    elif UC(E): uc+=1
    else: nuc+=1
print(f"  primitive 7-tuples: {tot}")
print(f"    Case 1 (site 0 free)                         {c1:>6} = {100*c1/tot:5.2f}%  -> witness at a/8")
print(f"    Case 2, crowding steerable (not Unit-Compl.) {nuc:>6} = {100*nuc/tot:5.2f}%  -> vacate 7, then speed cond.")
print(f"    Case 2, Unit-Complete (units fully occupied) {uc:>6} = {100*uc/tot:5.2f}%  -> no first-order direction")
