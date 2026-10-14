"""Search EXACTLY over rational profiles, where the true zeros live.  Start with integers: finite,
exhaustive, decidable.

Question: among integer profiles 1 < s_2 < ... < s_7, is the AP {2,3,4,5,6,7} the ONLY one with
uncovered length 0 on [1,7] u [9,15]?"""
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
for HI in (8, 12, 20, 30):
    zeros=[]; n=0
    for c in combinations(range(2,HI+1), 6):
        n+=1
        S=[F(x) for x in c]
        if joint(S)==0: zeros.append(c)
    print(f"  integer readings from 2..{HI}:  {n} profiles checked, {len(zeros)} with uncovered 0")
    for z in zeros[:6]:
        print(f"      {list(z)}   clear points {clear_pts([F(x) for x in z])}")
    if len(zeros)>6: print(f"      ... and {len(zeros)-6} more")
