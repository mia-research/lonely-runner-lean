"""
v2 -- supersedes twin_case_v1.py, which tracked only the residue r = 4 and so
reported a false cover at (e',m) = (11,4).  On part of I the residue r = 1 is also
uncovered, and a fibre is safe if ANY r survives.  v2 uses the full safe set.

Unit-Complete leaf, TWIN case: E = {1,3,5,7,rho0} u {e'} u {8m}, e' = 8q + rho'.
Safe x  <=>  union over ALL of E of bad(e, floor(e x)) != Z/8.
Exact rational arithmetic; cells cut by every j/e, e in E.
"""
from fractions import Fraction as F
from math import gcd
import sys

def bad(e,t): return frozenset(r for r in range(8) if (e*r+t)%8 in (0,7))
FULL=frozenset(range(8))

def safe_measure(E):
    pts={F(0),F(1)}
    for e in E:
        for j in range(1,e+1):
            q=F(j,e)
            if 0<q<1: pts.add(q)
    p=sorted(pts); tot=F(0); wins=[]
    for a,b in zip(p,p[1:]):
        x=(a+b)/2
        cov=set()
        for e in E: cov|=bad(e,int(e*x))
        if cov!=FULL:
            tot+=b-a; wins.append((a,b,sorted(FULL-cov)))
    return tot,wins

print("Check the tuple v1 flagged:  E = {1,3,4,5,7,11,32}")
E=(1,3,4,5,7,11,32); t,w=safe_measure(E)
print(f"   safe measure = {t} = {float(t):.5f};  {len(w)} safe cells")
for a,b,u in w[:8]: print(f"      x in [{a},{b})  uncovered r = {u}")
print()

print("Sweep the twin case, full safe set, rho0 = 4 (the hard residue):")
worst=None; zero=[]
for q in range(1,9):
    for rho2 in (1,3,5,7,4):
        e2=8*q+rho2
        for m in range(1,17):
            E=tuple(sorted({1,3,5,7,4,e2,8*m}))
            if len(E)!=7: continue
            g=0
            for e in E: g=gcd(g,e)
            if g!=1: continue
            t,_=safe_measure(E)
            if t==0: zero.append(E)
            if worst is None or t<worst[0]: worst=(t,E)
print(f"   tuples with ZERO safe measure: {len(zero)}")
if zero: print("      ",zero[:8])
print(f"   minimum safe measure {worst[0]} = {float(worst[0]):.6f}  at E = {worst[1]}")
