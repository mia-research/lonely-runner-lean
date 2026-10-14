"""Check the PROVED threshold b >= 10, and that b = 9 genuinely fails."""
from fractions import Fraction as F
import random
def blocks(si,A,sk):
    M=8*sk; r=(si*A)%M; return min(r,M-r)<sk
def band_pts(b,m,N):
    lo=F(b)*m+F(b,6); hi=F(b)*m+F(5*b,6)
    return [lo + F(i,N)*(hi-lo) for i in range(N+1)]
print("b >= 10: every rounding of every band point clears")
bad=0; n=0
for b in range(10,260):
    for m in (-7,-1,0,1,5,23):
        for t in band_pts(b,m,240):
            q=round(t)
            if abs(F(q)-t)>F(1,2): continue
            n+=1
            if blocks(1,8*q+1,b): bad+=1
print(f"   {n-bad}/{n} clear   {'(ALL, as proved)' if bad==0 else f'FAILS {bad}'}")
print("\nb = 8 and 9: the band contains points whose rounding is BLOCKED")
for b in (8,9):
    ex=[]
    for m in (0,1,2):
        for t in band_pts(b,m,400):
            q=round(t)
            if abs(F(q)-t)<=F(1,2) and blocks(1,8*q+1,b): ex.append((m,t,q)); break
    print(f"   b={b}: {len(ex)} blocked example(s), e.g. {ex[0] if ex else '-'}")
print("\nthe integrality gain: rational relaxation needs b>=15, integrality gives b>=10")
for b in range(8,17):
    rmax=(5*b+3)//6
    print(f"   b={b:2d}: max integer r with 6r <= 5b+3 is {rmax:3d};  8r+1 = {8*rmax+1:3d}  vs  7b = {7*b:3d}"
          f"   {'ok' if 8*rmax+1<=7*b else 'FAILS'}")
