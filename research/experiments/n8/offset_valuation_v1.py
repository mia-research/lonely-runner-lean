"""The (A) table is not a measurement, it is an orbit structure.

At grid instant p (p a unit mod 8) a runner at residue offset D sits at slot (D*p mod 8).  As p
ranges over the units, D*p ranges over the ORBIT of D under multiplication by (Z/8)^x.  Those
orbits are  {0}, {1,3,5,7}, {2,6}, {4}  -- i.e. the orbit of D is fixed by the 2-ADIC VALUATION
of D.  Conjecture to check: the closest a runner at offset D ever comes to the subject, over all
four grid instants, is exactly  2^nu(D) / 8.

Exhaustive over all offsets and all instants; no sampling."""
from fractions import Fraction as F
from math import floor
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nu2(d):
    if d==0: return None
    k=0
    while d%2==0: d//=2; k+=1
    return k
print("  D  nu2  slots over p=1,3,5,7      dists                 min      2^nu/8   match")
allok=True
for D in range(8):
    slots=[(D*p)%8 for p in (1,3,5,7)]
    dists=[circd(F(s,8)) for s in slots]
    mn=min(dists)
    if D==0:
        pred=F(0); nu='inf'
    else:
        nu=nu2(D); pred=F(2**nu,8)
    ok = (mn==pred)
    allok &= ok
    print(f"  {D}   {str(nu):>3}  {str(slots):<20} {str([str(x) for x in dists]):<34} {str(mn):<7}  {str(pred):<7}  {'OK' if ok else 'FAIL'}")
print(f"\n  all offsets agree: {allok}")
print()
print("  CONSEQUENCE for a GRID (pi a bijection, so the 7 offsets are exactly 1..7):")
tight=[D for D in range(1,8) if F(2**nu2(D),8)==F(1,8)]
never=[D for D in range(1,8) if F(2**nu2(D),8)>F(1,8)]
print(f"     can ever reach the threshold : offsets {tight}   ({len(tight)} of 7 runners)")
print(f"     structurally barred from it  : offsets {never}   ({len(never)} of 7 runners)")
for D in never:
    print(f"        offset {D}: never closer than {F(2**nu2(D),8)}  at ANY grid instant, in ANY arrangement")
