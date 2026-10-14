#!/usr/bin/env python3
"""v2: fixes the wrap bug (t=0 reported as good) and adds the OPENING LAW.
The k=0 bad arc is (-1/(8e), 1/(8e)) and WRAPS; clipping to [0,.) left {0} as a spurious
isolated good point.  t=0 is never good (every runner sits on the origin there)."""
from fractions import Fraction as F
from functools import reduce
from math import gcd
from itertools import combinations

def goodset(E):
    iv=[]
    for e in E:
        for k in range(0,e+1):
            lo,hi=max(F(8*k-1,8*e),F(0)),min(F(8*k+1,8*e),F(1))
            if lo<hi: iv.append((lo,hi))
    iv.sort(); m=[]
    for lo,hi in iv:
        if m and lo<m[-1][1]: m[-1][1]=max(m[-1][1],hi)   # STRICT: open sets
        else: m.append([lo,hi])
    g=[]; cur=F(0)
    for lo,hi in m:
        if cur<=lo: g.append((cur,lo))
        cur=max(cur,hi)
    if cur<=1: g.append((cur,F(1)))
    # WRAP FIX: 0 and 1 are the same point of the circle and are always BLOCKED
    return [(a,b) for a,b in g if a<=b and not (a==b==0) and not (a==b==1)]
def meas(G): return sum(b-a for a,b in G)
def clear(V):
    q=reduce(lambda a,b:a*b//gcd(a,b),[x.denominator for x in V])
    E=[int(x*q) for x in V]; g=reduce(gcd,E)
    return tuple(e//g for e in E), q//g

print("BUG FIX CHECK -- t=0 must never be in Gbar")
for E in ((1,2,3,4,5,6,7),(2,6,7,8,10,13,14),(1,3,5,7,9,11,13)):
    G=goodset(E)
    print(f"  {E}: contains 0 -> {any(a<=0<=b for a,b in G)}   |Gbar|={meas(G)}  comps={len(G)}")
print("  AP Gbar =", [f"{{{a}}}" if a==b else f"[{a},{b}]" for a,b in goodset((1,2,3,4,5,6,7))])

print("\nRE-VERIFY the two exhaustive numbers of GRID_TRACKING_v1 under the fix")
def dist_to_grid(E):
    G=goodset(E); best=None
    for a in (1,3,5,7):
        p=F(a,8)
        for lo,hi in G:
            d=F(0) if lo<=p<=hi else min(abs(p-lo),abs(p-hi))
            if best is None or d<best: best=d
    return best
c1=c1b=0; worst=(F(0),None); n2=0
for E in combinations(range(1,19),7):
    if reduce(gcd,E)!=1: continue
    if all(e%8 for e in E):
        c1+=1
        if dist_to_grid(E)!=0: c1b+=1
    else:
        n2+=1
        d=dist_to_grid(E)
        if d>worst[0]: worst=(d,E)
print(f"  Case 1 ({c1} tuples): nonzero grid distance in {c1b}  {'PASS' if c1b==0 else 'FAIL'}")
print(f"  Case 2 ({n2} tuples): max grid distance {worst[0]} = {float(worst[0]):.6f} at {worst[1]}")
print(f"  GRID_TRACKING_v1 reported max = 1/10 at (1,2,3,5,6,7,8) -> "
      f"{'UNCHANGED' if worst[0]==F(1,10) else 'CHANGED'}")

print("\n" + "="*76)
print("THE OPENING LAW at t=1/8.  Only the residue-1 and residue-7 runners bind.")
print("Perturb runner 1 upward, w = 1+d: predicted interval [1/(8w), 1/8], length (w-1)/(8w)")
print(f"  {'w':>7} {'predicted':>12} {'measured':>12}  match")
for num in range(11,21):
    w=F(num,10)
    V=[w]+[F(i) for i in range(2,8)]
    E,q=clear(V); G=goodset(E); s=F(1,8*q)
    comp=[(a,b) for a,b in G if a<=s<=b]
    pred=(w-1)/(8*w)
    got=(comp[0][1]-comp[0][0])*q if comp else F(0)
    print(f"  {str(w):>7} {str(pred):>12} {str(got):>12}  {pred==got}")
print("\nPerturb runner 7 downward, w = 7-d: runner 7 forces t <= 1/(8)*(7/w)... measure it")
print(f"  {'w':>7} {'|Gbar|':>14}  interval containing 1/8 (scaled), length")
for num in range(70,59,-1):
    w=F(num,10)
    V=[F(i) for i in range(1,7)]+[w]
    E,q=clear(V); G=goodset(E); s=F(1,8*q)
    comp=[(a,b) for a,b in G if a<=s<=b]
    L=(comp[0][1]-comp[0][0])*q if comp else None
    print(f"  {str(w):>7} {str(meas(G)):>14}  {'len '+str(L) if L is not None else 't=1/8 LOST'}")
