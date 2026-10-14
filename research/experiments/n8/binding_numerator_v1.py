"""Their item 3 (band-2 unreachability) is the whole problem.  One concrete reformulation:

R is the first clear point, and at the R-maximisers it equals (8k+1)/s for the binding reading s.
Since S > 7 for any non-trivial profile, R = (8k+1)/S < 16 would follow from (8k+1) < 112, i.e.
k <= 13.  So: IS THE BINDING LAP INDEX BOUNDED?

Measure the binding (8k+1) -- the numerator at the clear point -- across profiles, and see whether
it is bounded and how it relates to R.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor
import random
from collections import Counter
def Rdir_exact(ds, RMAX=60):
    c=F(min(ds)); S=[F(d)/c for d in ds]
    cand=[(F(1),None,None)]
    for s in S:
        k=0
        while F(8*k+1)/s<=RMAX:
            r=F(8*k+1)/s
            if r>=1: cand.append((r,8*k+1,s))
            k+=1
    for R,num,s in sorted(set(cand), key=lambda z:(z[0], -1 if z[1] is None else z[1])):
        if all(1 <= (t*R) % 8 <= 7 for t in S): return R,num,s
    return None,None,None
rng=random.Random(606)
nums=Counter(); rows=[]
for _ in range(4000):
    v=speeds(rng.sample(range(1,120),8))
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        R,num,s=Rdir_exact(ds)
        if R is None: continue
        nums[num]+=1; rows.append((float(R), num, float(s) if s else None))
print(f"  {len(rows)} subjects\n")
print(f"  binding numerator (8k+1) at the clear point, distribution:")
print(f"    {dict(sorted(nums.items(), key=lambda x:(x[0] is None, x[0]))[:12])}")
mx=max((n for n in nums if n is not None), default=None)
print(f"    maximum binding numerator : {mx}")
print(f"    R = 1 (no numerator)      : {nums.get(None,0)}")
print()
print("  on the known deep cases and the R-maximisers:")
KNOWN=[("23-move",[30,74,96,127,159,175,224]),("28-move",[49,205,234,256,286,323,366]),
       ("R=11.62",[46,107,146,194,241,268,344]),("R=11.93",[158,367,505,664,827,918,1179]),
       ("R=11.96",[2520,5750,8003,10557,13161,14580,18745])]
for nm,ds in KNOWN:
    R,num,s=Rdir_exact(ds)
    print(f"    {nm:>9}: R = {float(R):.6f}   binding (8k+1) = {num}   s = {float(s):.4f}   "
          f"check (8k+1)/s = {num/float(s):.6f}")
print()
print("  R < 16 would follow from (8k+1) < 16.S.  With S > 7 that is (8k+1) < 112, i.e. k <= 13.")
print(f"  observed maximum k : {(mx-1)//8 if mx else None}")
print("  -> bounding the binding lap index is EQUIVALENT to the bound, not easier;")
print("     nothing here bounds it, and a large k with a large s gives a small R anyway.")
