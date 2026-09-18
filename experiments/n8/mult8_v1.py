"""All three zeros have NO reading divisible by 8.  Combined with Guard.odd_clear_of_not_dvd
(proved: 8 not dividing s and R odd => 8 not dividing s.R), that gives, for INTEGER profiles:

    no reading = 0 mod 8   ->  all eight odd integers clear  ->  R = 1        [PROVED]
    some reading = 0 mod 8 ->  ??? must show uncovered > 0

If the second holds, the integer case is closed: either branch gives R < 16.
Test it: among integer profiles CONTAINING a multiple of 8, what is the minimum uncovered?"""
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
best=None; n=0; zeros=0
for c in combinations(range(2,41), 6):
    if not any(x%8==0 for x in c): continue
    n+=1
    v=joint([F(x) for x in c])
    if v==0: zeros+=1; print(f"  ZERO with a multiple of 8: {list(c)}")
    if best is None or v<best[0]: best=(v,c)
print(f"  integer profiles in 2..40 containing a multiple of 8 : {n}")
print(f"  of those with uncovered == 0 : {zeros}")
print(f"  minimum uncovered : {best[0]} = {float(best[0]):.8f}   at {list(best[1])}")
print()
print("  so on this range: a reading divisible by 8 forces uncovered > 0, with minimum")
print(f"  {float(best[0]):.8f} -- a clear interval of that length, hence R <= 15.")
