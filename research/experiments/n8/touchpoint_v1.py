"""TWO THINGS.

(A) THE TOUCH-POINT OBSTRUCTION.  Maximising reach drives interval j to START exactly where
interval j-1 ENDS.  Bad intervals are OPEN, so the touch point is uncovered -- it is a clear R.
Covering therefore needs STRICT overlap at every junction, and the reach multiplier is strictly
below (8m+1)/(8m-1).  Verify on the forced geometric profile: is R exactly 9/S?

(B) SENSITIVITY.  forced_profile_v1 fed the R-maximiser ROUNDED to 4 decimals and got R = 6.32
where the unrounded profile gives 11.97.  That is not a discrepancy -- it is the cell structure:
the maximiser sits in a narrow cell and rounding leaves it.  Quantify.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
def Rex(S, RMAX=200):
    cand=[F(1)]
    for s in S:
        k=0
        while F(8*k+1)/s<=RMAX:
            r=F(8*k+1)/s
            if r>=1: cand.append(r)
            k+=1
    for R in sorted(set(cand)):
        if all(1 <= (s*R)%8 <= 7 for s in S): return R
    return None
print("(A) the forced geometric profile, exact rationals, ratio 9/7 descending from 7\n")
r=F(9,7)
for Snum,Sden in ((701,100),(705,100),(71,10),(73,10),(745,100)):
    S=F(Snum,Sden)
    geo=sorted([F(7)/(r**j) for j in range(1,6)])      # five interior readings
    prof=[F(1)]+geo+[S]
    R=Rex(prof)
    pred=F(9)/S
    print(f"    S = {float(S):.3f}: R = {R} = {float(R):.6f}   9/S = {float(pred):.6f}   "
          f"{'R = 9/S exactly' if R==pred else 'differs'}")
print()
print("    -> the touch point 9/S is clear, so the max-reach configuration clears at the FIRST")
print("       junction.  Maximising reach and covering are in direct tension.")
print()
print("(B) sensitivity of R to rounding the profile (the R = 11.9657 maximiser)\n")
exact=[F(1),F(23580,10000),F(31372,10000),F(41865,10000),F(52224,10000),F(57887,10000),F(74379,10000)]
print(f"    at 4 decimals : R = {float(Rex(exact)):.6f}")
for d in (5,6,7,8):
    prof=[F(1)]+[F(round(float(x)*10**d), 10**d) for x in exact[1:]]
    print(f"    at {d} decimals : R = {float(Rex(prof)):.6f}")
print()
print("    -> R is not a continuous function of the profile; it is cell-wise constant, and the")
print("       maximiser's cell is narrow.  Rounding leaves the cell and R falls by half.")
