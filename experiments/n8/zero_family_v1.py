"""The first-order rates are ZERO on the non-units 2,4,6 -- so the zero set of the uncovered-length
functional is a FAMILY, not the isolated AP.  My uniqueness claim in REDUCTION_v1 is wrong.

But the reduction may survive in better shape: the eight protected points are guarded by the UNITS
(1,3,5,7), which the family leaves untouched.  So every member should still have those eight points
CLEAR -- non-empty clear set, R < 16.

Test both: (a) how far can 2,4,6 move with uncovered still exactly 0?
           (b) are the eight odd integers clear throughout?"""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
def unc_exact(S, lo, hi):
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
def joint(S): return unc_exact(S,1,7)+unc_exact(S,9,15)
def clear_pts(S):
    """which of the eight odd integers are clear for readings S together with s_1 = 1"""
    out=[]
    for R in (1,3,5,7,9,11,13,15):
        if all(1 <= (s*R) % 8 <= 7 for s in [F(1)]+list(S)): out.append(R)
    return out
print("  (a) moving the NON-UNITS 2, 4, 6 -- how far does uncovered stay 0?\n")
print(f"  {'reading 2':>12} {'joint uncovered':>18} {'clear odd integers':>22}")
for num,den in ((2,1),(21,10),(23,10),(25,10),(28,10),(29,10),(295,100),(299,100)):
    s2=F(num,den)
    S=[s2,F(3),F(4),F(5),F(6),F(7)]
    if s2>=3: break
    print(f"  {str(s2):>12} {str(joint(S)):>18} {str(clear_pts(S)):>22}")
print()
print("  moving all three non-units together:")
for d in (F(0), F(1,10), F(3,10), F(1,2), F(7,10), F(9,10)):
    S=sorted([F(2)+d, F(4)+d, F(6)+d, F(3), F(5), F(7)])
    print(f"    shift {str(d):>6}: readings {[str(x) for x in S]}")
    print(f"      joint uncovered {joint(S)}   clear odd integers {clear_pts(S)}")
print()
print("  (b) and if a UNIT moves, the guard goes:")
for lab,S in (("3 -> 3.1",[F(2),F(31,10),F(4),F(5),F(6),F(7)]),
              ("5 -> 5.1",[F(2),F(3),F(4),F(51,10),F(6),F(7)]),
              ("7 -> 7.1",[F(2),F(3),F(4),F(5),F(6),F(71,10)])):
    print(f"    {lab}: joint uncovered {float(joint(S)):.8f}   clear odd integers {clear_pts(S)}")
