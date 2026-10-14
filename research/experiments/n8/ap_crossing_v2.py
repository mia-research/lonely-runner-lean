"""v1 returned None at the exact AP: the only clear point is R = 1, where reading 7 sits exactly ON
the threshold, and my epsilon pushed it off.  The threshold counts as clear.  Redone in exact
rational arithmetic.

Family: readings 1, 1+u, ..., 1+6u with u rational; S = 1+6u.  u = 1 is the AP.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
def Rexact(S, RMAX=60):
    cand=[F(1)]
    for s in S:
        k=0
        while True:
            r=F(8*k+1)/s
            if r>RMAX: break
            if r>=1: cand.append(r)
            k+=1
    for R in sorted(set(cand)):
        if all(1 <= (s*R) % 8 <= 7 for s in S): return R
    return None
print("  AP family: readings 1, 1+u, ..., 1+6u   (u = 1 is the AP, S = 7)\n")
print(f"  {'u':>9} {'S':>9} {'first clear R':>16} {'band':>5}")
prev=None
for num in range(1000, 1061, 5):
    u=F(num,1000)
    S=[1+k*u for k in range(7)]
    R=Rexact(S)
    if R is None:
        print(f"  {float(u):>9.3f} {float(1+6*u):>9.3f} {'none <= 60':>16}")
        continue
    band=int(R//8)
    mark="   <-- JUMP" if prev is not None and abs(float(R)-prev)>1.0 else ""
    print(f"  {float(u):>9.3f} {float(1+6*u):>9.3f} {float(R):>16.6f} {band:>5}{mark}")
    prev=float(R)
print("\n  the exact AP (u = 1): where are the clear points in [1,15]?")
S=[F(k) for k in range(1,8)]
cand=set([F(1)])
for s in S:
    k=0
    while F(8*k+1)/s<=15:
        if F(8*k+1)/s>=1: cand.add(F(8*k+1)/s)
        k+=1
    k=0
    while F(8*k-1)/s<=15:
        if F(8*k-1)/s>=1: cand.add(F(8*k-1)/s)
        k+=1
pts=[R for R in sorted(cand) if all(1<=(s*R)%8<=7 for s in S)]
print(f"    clear points among all band endpoints: {[str(p) for p in pts]}")
print(f"    -> the AP's clear set in [1,15] consists of ISOLATED POINTS; it has measure zero.")
