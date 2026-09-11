#!/usr/bin/env python3
"""THE TRANSITION MAP at the AP (owner's idea).

Base E = (1,2,3,4,5,6,7) with a stationary runner at 0 -- the tight instance T1.
Perturb ONE speed continuously (v = 2 -> 1.9, 1.8, ... and 2.1, 2.2, ...) and map exactly
what the good set does.  Rational speeds are cleared to integers (LRC is dilation-invariant:
||(e/q) t|| >= 1/8  <=>  ||e (t/q)|| >= 1/8), so all arithmetic stays exact.
"""
from fractions import Fraction as F
from functools import reduce
from math import gcd

def goodset(E):
    """closed {t : ||e t|| >= 1/8}.  Bad sets are OPEN, so merge with STRICT <."""
    iv=[]
    for e in E:
        for k in range(0,e+1):
            lo,hi=max(F(8*k-1,8*e),F(0)),min(F(8*k+1,8*e),F(1))
            if lo<hi: iv.append((lo,hi))
    iv.sort(); m=[]
    for lo,hi in iv:
        if m and lo<m[-1][1]: m[-1][1]=max(m[-1][1],hi)
        else: m.append([lo,hi])
    g=[]; cur=F(0)
    for lo,hi in m:
        if cur<=lo: g.append((cur,lo))
        cur=max(cur,hi)
    if cur<=1: g.append((cur,F(1)))
    return [(a,b) for a,b in g if a<=b]
def meas(G): return sum(b-a for a,b in G)
def clear(V):
    q=reduce(lambda a,b:a*b//gcd(a,b),[x.denominator for x in V])
    E=[int(x*q) for x in V]; g=reduce(gcd,E)
    return tuple(e//g for e in E), q//g   # integer tuple, and the scale
def show(G,lim=6):
    s=[f"[{a},{b}]" if a!=b else f"{{{a}}}" for a,b in G]
    return ", ".join(s[:lim])+(" ..." if len(G)>lim else "")

AP=[F(i) for i in range(1,8)]
G0=goodset(tuple(range(1,8)))
print("BASE  E = (1,2,3,4,5,6,7)")
print(f"  Gbar = {show(G0)}   |Gbar| = {meas(G0)}   components = {len(G0)}")
print("  -> four isolated points, the grid times. This is the tight instance T1.")
print("\n  who binds at t = 1/8?  ||e/8|| for e = 1..7:")
print("   ", {e: str(min(F(e,8)%1, 1-F(e,8)%1)) for e in range(1,8)})
print("  runners 1 and 7 sit exactly at 1/8; 1 forces t>=1/8, 7 forces t<=1/8.")

print("\n" + "="*76)
print("PERTURB RUNNER 2 (the one you named): v = 2 + d")
print(f"  {'v':>6} {'integer tuple (cleared)':>34} {'|Gbar|':>12}  components / witness at 1/8?")
for num in range(11,30):
    v=F(num,10)
    V=[F(1),v]+[F(i) for i in range(3,8)]
    E,q=clear(V)
    G=goodset(E)
    # the ORIGINAL t corresponding to integer s is t = q*s; witness at t=1/8 <=> s=1/(8q)
    s=F(1,8*q)
    at=any(a<=s<=b for a,b in G)
    print(f"  {str(v):>6} {str(E):>34} {str(meas(G)):>12}  {len(G):>3} comps   t=1/8 witness: {at}")

print("\n" + "="*76)
print("PERTURB RUNNER 1 (a BINDING runner): v = 1 + d  -- the transition")
print(f"  {'v':>7} {'|Gbar|':>14} {'components':>11}   Gbar near the 1/8 grid point")
for num in list(range(6,16)):
    v=F(num,10)
    V=[v]+[F(i) for i in range(2,8)]
    E,q=clear(V)
    G=goodset(E)
    s=F(1,8*q)
    near=[(a,b) for a,b in G if abs((a+b)/2 - s) < F(1,4*q)]
    print(f"  {str(v):>7} {str(meas(G)):>14} {len(G):>11}   "
          f"{'t=1/8 IS a witness' if any(a<=s<=b for a,b in G) else 't=1/8 LOST'}"
          f"   nearest comps: {show(near,2) if near else '(none nearby)'}")
