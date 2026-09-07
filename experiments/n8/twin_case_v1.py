"""
Unit-Complete leaf, TWIN case: |E_non| = 6, |E_div| = 1.
E = {1,3,5,7,rho0} u {e'} u {8m},  e' = 8q + rho' with q >= 1, rho' in R_non.

Hardest sub-case rho0 = 4.  On I = [1/4, 3/7) the five base runners leave r = 4
uncovered THROUGHOUT (from safe_measure_v1: windows {4}, {1,4}, {4} tile I).
Since divisible runners do not depend on r, the only extra killer of r = 4 is the twin.

r = 4 in bad(e',t')  <=>  4e' + t' = 0 or 7 (mod 8).
  e' odd  : 4e' = 4 (mod 8)  ->  t' in {3,4}
  e' even : 4e' = 0 (mod 8)  ->  t' in {0,7}
So the twin kills  A(e') = {x : floor(e' x) mod 8 in K},  K = {3,4} or {0,7}:
intervals of length 2/e' spaced 8/e', measure 1/4.
The divisible runner kills B_m = {x : floor(8m x) mod 8 in {0,7}} = {x : ||m x|| < 1/8}.

QUESTION: can A(e') u B_m cover I?  Exact rational arithmetic.
"""
from fractions import Fraction as F
import sys

def A(c, K, lo=F(0), hi=F(1)):
    """{x in [lo,hi) : floor(c x) mod 8 in K} as disjoint intervals."""
    out=[]
    t=int(c*lo)
    while F(t,c) < hi:
        if t%8 in K:
            a,b=max(F(t,c),lo), min(F(t+1,c),hi)
            if a<b: out.append((a,b))
        t+=1
    merged=[]
    for a,b in sorted(out):
        if merged and a<=merged[-1][1]: merged[-1][1]=max(merged[-1][1],b)
        else: merged.append([a,b])
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

I=(F(1,4),F(3,7))
print(f"I = [1/4,3/7), |I| = {F(3,7)-F(1,4)} = {float(F(3,7)-F(1,4)):.5f}")
worst=None; covers=[]
EMAX, MMAX = 400, 50
for e2 in range(9, EMAX+1):
    K={3,4} if e2%2 else {0,7}
    Ae=A(e2,K,I[0],I[1])
    for m in range(1, MMAX+1):
        Bm=A(8*m,{0,7},I[0],I[1])
        g=uncovered(I, Ae+Bm)
        tot=sum(b-a for a,b in g)
        if tot==0: covers.append((e2,m))
        if worst is None or tot<worst[0]: worst=(tot,e2,m,g)
print(f"twin speeds e' in [9,{EMAX}] x divisible m in [1,{MMAX}]: "
      f"{(EMAX-8)*MMAX} pairs")
print(f"pairs where A(e') u B_m COVERS I entirely: {len(covers)}")
if covers: print("   first few:", covers[:15])
t,e2,m,g=worst
print(f"minimum surviving measure {t} = {float(t):.6f} at (e'={e2}, m={m})")
print(f"   surviving gaps {[(str(a),str(b)) for a,b in g]}")
print()
print("gap-argument thresholds:  A(c) has components 2/c spaced 8/c, so I contains a")
print(f"full gap of A(c) (length 6/c) once 8/c <= |I| = 5/28, i.e. c >= 224/5 = 44.8.")
print("For B_m, c = 8m, so that is m >= 6.  Both large -> 6/c1 <= 2/c2 and 6/c2 <= 2/c1,")
print("i.e. c1 >= 3c2 and c2 >= 3c1: impossible.  Small c is the finite table above.")
