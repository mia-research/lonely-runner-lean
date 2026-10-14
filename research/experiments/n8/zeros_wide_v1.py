"""Three integer zeros found, all with the same eight clear points.  Widen the EXACT search and test
the one thing the reduction needs:

    does ANY profile with uncovered length 0 have an EMPTY clear set?

An empty clear set is band 2.  Search integers to 40 and half-integers, exactly."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from itertools import combinations
def unc(S, lo, hi):
    bad=[]
    for s in S:
        k=0
        while F(8*k-1,1)/s <= hi+1:
            a,b=F(8*k-1,1)/s, F(8*k+1,1)/s
            if b>lo and a<hi: bad.append((max(a,F(lo)),min(b,F(hi))))
            k+=1
    bad.sort(); merged=[]
    for a,b in bad:
        if merged and a<=merged[-1][1]: merged[-1]=(merged[-1][0],max(merged[-1][1],b))
        else: merged.append((a,b))
    u=F(hi)-F(lo)
    for a,b in merged: u-=(b-a)
    return u
def joint(S): return unc(S,1,7)+unc(S,9,15)
def clear_pts(S):
    return [R for R in (1,3,5,7,9,11,13,15) if all(1 <= (s*R)%8 <= 7 for s in [F(1)]+list(S))]
def guard_res(S):
    """which unit residues mod 8 the profile supplies (integers only)"""
    return sorted({int(s)%8 for s in S if s.denominator==1 and int(s)%2==1})
print("  === integers 2..40 ===")
zeros=[]; n=0
for c in combinations(range(2,41), 6):
    n+=1
    S=[F(x) for x in c]
    if joint(S)==0: zeros.append(c)
print(f"  {n} profiles, {len(zeros)} zeros")
print(f"  {'profile':>26} {'clear points':>34} {'odd residues mod 8':>20}")
for z in zeros:
    S=[F(x) for x in z]
    print(f"  {str(list(z)):>26} {str(clear_pts(S)):>34} {str(guard_res(S)):>20}")
empty=[z for z in zeros if not clear_pts([F(x) for x in z])]
print(f"\n  zeros with EMPTY clear set: {len(empty)}  {empty}")
print()
print("  === half-integers 3/2 .. 20 (denominators 1 and 2) ===")
vals=[F(k,2) for k in range(3,41)]
zeros2=[]; n2=0
for c in combinations(vals, 6):
    n2+=1
    if joint(list(c))==0: zeros2.append(c)
print(f"  {n2} profiles, {len(zeros2)} zeros")
for z in zeros2[:10]:
    print(f"    {[str(x) for x in z]}   clear {clear_pts(list(z))}")
if len(zeros2)>10: print(f"    ... and {len(zeros2)-10} more")
empty2=[z for z in zeros2 if not clear_pts(list(z))]
print(f"\n  zeros with EMPTY clear set: {len(empty2)}")
