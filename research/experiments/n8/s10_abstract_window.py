"""S10: the sharp form of task Point 1.
Question: does there exist a real x in a window W and unit speeds e_rho = rho mod 8
(rho = 1,3,5,7, any positive integers) such that the four unit runners
  bad(rho, floor(e_rho * x))
already cover Z/8 ?
Decidable: floor(e x) is piecewise constant with breakpoints j/e, so scan cells
with EXACT rational midpoints.  Bound e <= EMAX."""
import sys
from fractions import Fraction as F
from itertools import product
from n8_fibre_core import bad

EMAX = int(sys.argv[1]) if len(sys.argv)>1 else 200

WINDOWS = [("[2/7,2/5)", F(2,7), F(2,5), "{1,4}"),
           ("[3/5,5/7)", F(3,5), F(5,7), "{3,6}")]

def speeds(rho, emax):
    return [e for e in range(rho, emax+1, 8) if e>0]

for name, lo, hi, exp in WINDOWS:
    pts = {lo, hi}
    for rho in (1,3,5,7):
        for e in speeds(rho, EMAX):
            j0 = (e*lo.numerator)//lo.denominator
            j = j0
            while F(j, e) < hi:
                if lo < F(j,e) < hi: pts.add(F(j,e))
                j += 1
    pts = sorted(pts)
    hits = []
    minunc = 9
    minrec = None
    for i in range(len(pts)-1):
        mid = (pts[i]+pts[i+1])/2
        # for each rho collect achievable blocked pairs at this x
        S = {}
        for rho in (1,3,5,7):
            s=set()
            for e in speeds(rho, EMAX):
                t = (e*mid.numerator)//mid.denominator
                s.add(bad(rho, t))
            S[rho]=sorted(s, key=lambda z: sorted(z))
        best=9; bestc=None
        for combo in product(S[1],S[3],S[5],S[7]):
            u=set()
            for c in combo: u|=c
            if len(u)<8:
                if 8-len(u)<best:
                    best=8-len(u); bestc=combo
            else:
                hits.append((pts[i],pts[i+1],combo)); best=0; bestc=combo; break
        if best<minunc:
            minunc=best; minrec=(pts[i],pts[i+1],bestc)
    print(f"window {name}  (representative table says uncovered {exp})")
    print(f"  cells scanned: {len(pts)-1}   speeds per class up to {EMAX}")
    print(f"  cells where the 4 units can cover ALL of Z/8: {len(hits)}")
    print(f"  minimum achievable |uncovered| over all cells and all speed choices: {minunc}")
    if hits:
        lo2,hi2,combo = hits[0]
        print(f"  EXAMPLE: x in ({lo2},{hi2}), blocked pairs {[sorted(c) for c in combo]}")
    print()
