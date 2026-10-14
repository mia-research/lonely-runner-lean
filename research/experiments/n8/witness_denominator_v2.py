"""
v2 -- the EXHAUSTIVE tail of D(T), which v1's random sampling could not see.

D(T) = min{ q>=2 : some a coprime to q has ||v a/q|| >= 1/8 for all v in T }.

v1 measured max D over 600 random residual sets per speed bound and got a flat ~21.
That is close to FORCED for a random set: there are about 175 pairs (a,q) with q<=23,
each works with probability about (3/4)^7 = 0.133 if residues were uniform, so the
chance none works is about e^-25.  Random sampling therefore measures the bulk and is
blind to the tail -- and the tail is the entire question.  This run takes the maximum
over EVERY residual set up to a speed bound.

Also reported: D on the three exhaustive minimisers of M over the residual case
(M = 2/15), which are the sets whose good set is smallest and so the likeliest to
need a large denominator.

CONTROL (must fire).  The same routine at threshold 1/7 on the three tight instances:
they have M = 1/8 < 1/7, so NO q can work and D must come back None.  If it does not,
the harness is wrong and every number here is void.
"""
from itertools import combinations
from math import gcd
import sys

def D(T, qmax, num=1, den=8):
    for q in range(2, qmax+1):
        for a in range(1, q):
            if gcd(a,q)!=1: continue
            ok=True
            for v in T:
                r=(v*a)%q
                if den*min(r,q-r) < num*q: ok=False; break
            if ok: return q
    return None

def in_R(T):
    if not all(any(v%m==0 for v in T) for m in (5,6,7,8)): return False
    g=0
    for v in T: g=gcd(g,v)
    return g==1

print("CONTROL at threshold 1/7 on the three tight instances (M = 1/8 < 1/7):")
fired=True
for T in [(1,2,3,4,5,6,7),(1,2,3,4,5,7,12),(1,4,5,6,7,11,13)]:
    d=D(T,200,1,7); fired &= (d is None)
    print(f"   {T}: D@(1/7) = {d}  {'ok' if d is None else '*** SHOULD BE None'}")
print("CONTROL", "FIRES" if fired else "*** FAILED -- results below are void", flush=True)

print("\nD on the exhaustive minimisers of M over the residual case (M = 2/15):")
for T in [(1,3,4,5,7,11,24),(1,4,5,6,7,11,16),(2,6,7,8,10,13,14)]:
    print(f"   {T}: D = {D(T,400)}", flush=True)

print("\nEXHAUSTIVE max D over the residual case:")
QMAX=600
for V in (16,20,24,28):
    mx=0; worst=None; n=0; none=0
    for T in combinations(range(1,V+1),7):
        if not in_R(T): continue
        n+=1
        d=D(T,QMAX)
        if d is None: none+=1; continue
        if d>mx: mx,worst=d,T
    print(f"  V={V:>3}: {n:>7} residual sets   max D = {mx:>4}  (at {worst})"
          f"   unresolved q<= {QMAX}: {none}", flush=True)
