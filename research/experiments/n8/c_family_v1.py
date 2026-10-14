"""Flank e is clear at multiplier c (c = 1 mod 8) iff dist(c*d_j, 8e*Z) >= e for all j.
c = -7 is one choice; c = 1 is another.  How large must |c| be allowed before SOME flank of
SOME subject clears?  If a small fixed family of c always suffices, that is a finite criterion."""
from math import gcd
import random, sys
def clearAt(ds,e,c):
    M=8*e
    for d in ds:
        r=(c*d)%M
        if min(r,M-r)<e: return False
    return True
def minC(ds, cs):
    """smallest |c| in the list that clears SOME flank of this subject; None if none do"""
    flanks=sorted({abs(d) for d in ds})
    for c in cs:
        for e in flanks:
            if clearAt(ds,e,c): return c
    return None
CS=sorted({1+8*t for t in range(-400,401)}, key=lambda c:(abs(c),c))
random.seed(7)
print("worst-case smallest |c| clearing some flank, over random integer subjects")
for hi in (12,30,100,400):
    worst=0; worstv=None; fails=0; n=0
    for _ in range(30000):
        v=random.sample(range(-hi,hi+1),8); s=random.randrange(8)
        ds=[v[j]-v[s] for j in range(8) if j!=s]
        n+=1
        c=minC(ds,CS)
        if c is None: fails+=1; continue
        if abs(c)>abs(worst): worst,worstv=c,(v,s)
    print(f"  range +-{hi:4d}: max over {n} subjects of min |c| = {abs(worst)}  (c={worst}); "
          f"no c found in |c|<=3200: {fails}")
    if worstv: print(f"      attained at v={worstv[0]} subject {worstv[1]}")
