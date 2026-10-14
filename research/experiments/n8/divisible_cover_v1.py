"""
Can the two divisible runners kill the whole safe set?

Setting: n=8, Case 2, Unit-Complete, representative speeds.  E_non = {1,3,5,7,rho0},
E_div = {8*m1, 8*m2} with m1 != m2 positive integers.

Identity [PROVED]: for e = 8m, bad(e, floor(e*b/L), 8) = Z/8  iff  floor(8m x) mod 8
in {0,7}  iff  8m x mod 8 in [0,1) u [7,8)  iff  ||m x|| < 1/8, where x = b/L.
So the divisible runner 8m contributes exactly the condition ||m x|| >= 1/8, and its
bad set is B_m = {x : ||m x|| < 1/8}: intervals of length 1/(4m) centred at j/m,
total measure 1/4.

Safe set of the five non-divisible runners (computed exactly in safe_measure_v1.py):
   rho0 = 2 : measure 22/35   rho0 = 4 : [1/4,3/7) u [4/7,3/4), measure 5/14
   rho0 = 6 : measure 6/7
For rho0 = 2 and 6, 1 - 2*(1/4) = 1/2 < measure, so the union bound already gives a
surviving point.  rho0 = 4 has measure 5/14 < 1/2 and needs the structure.

QUESTION: can B_{m1} u B_{m2} cover [1/4, 3/7) (length 5/28)?  Exact interval
arithmetic, no floating point.
"""
from fractions import Fraction as F
import sys

def B(m):
    """{x in [0,1) : ||m x|| < 1/8} as a sorted list of disjoint half-open intervals."""
    out=[]
    for j in range(0,m+1):
        lo,hi=F(j,m)-F(1,8*m), F(j,m)+F(1,8*m)
        lo,hi=max(lo,F(0)),min(hi,F(1))
        if lo<hi: out.append((lo,hi))
    out.sort(); merged=[]
    for lo,hi in out:
        if merged and lo<=merged[-1][1]: merged[-1][1]=max(merged[-1][1],hi)
        else: merged.append([lo,hi])
    return [(a,b) for a,b in merged]

def uncovered(win, ivs):
    lo,hi=win; cur=lo; gaps=[]
    for a,b in sorted(ivs):
        if b<=cur or a>=hi: continue
        if a>cur: gaps.append((cur,a))
        cur=max(cur,b)
        if cur>=hi: break
    if cur<hi: gaps.append((cur,hi))
    return gaps

WIN=(F(1,4),F(3,7))
M=80
worst=None; covered=[]
for m1 in range(1,M+1):
    for m2 in range(m1+1,M+1):
        g=uncovered(WIN, B(m1)+B(m2))
        tot=sum(b-a for a,b in g)
        if tot==0: covered.append((m1,m2))
        if worst is None or tot<worst[0]: worst=(tot,m1,m2,g)
print(f"window [1/4,3/7), length {F(3,7)-F(1,4)} = {float(F(3,7)-F(1,4)):.5f}")
print(f"pairs (m1,m2) with 1 <= m1 < m2 <= {M}: {M*(M-1)//2}")
print(f"pairs whose two bad sets COVER the window entirely: {len(covered)}")
if covered: print("   ", covered[:20])
t,a,b,g=worst
print(f"minimum surviving measure = {t} = {float(t):.6f}  at (m1,m2)=({a},{b})")
print(f"   surviving gaps: {[(str(u),str(v)) for u,v in g]}")
