# Is  min W*d_max = 1/n  a pattern, or a coincidence at (n=5, 3 blockers)?
from fractions import Fraction as F
from itertools import combinations
import math
def norm(x): return min(x - (x.numerator//x.denominator), 1 - (x - (x.numerator//x.denominator)))
def W(ds, n):
    pts={F(0),F(1)}
    for d in ds:
        for k in range(0,d+2):
            for off in (F(-1,n),F(1,n)):
                t=(F(k)+off)/F(d)
                if 0<=t<=1: pts.add(t)
    P=sorted(pts); best=F(0)
    for i in range(len(P)-1):
        lo,hi=P[i],P[i+1]
        if all(norm(F(d)*((lo+hi)/2))>=F(1,n) for d in ds) and hi-lo>best: best=hi-lo
    return best
print(f"{'n':>3} {'blockers':>9} {'HI':>4} {'min W*dmax':>12} {'= 1/n?':>8}  argmin")
for n in (5,6,7,8):
    for k in (2,3,4):
        HI = 26 if k<=3 else 16
        best=None; arg=None
        for ds in combinations(range(1,HI+1),k):
            g=ds[0]
            for x in ds[1:]: g=math.gcd(g,x)
            if g!=1: continue
            v=W(ds,n)*ds[-1]
            if best is None or v<best: best,arg=v,ds
        print(f"{n:>3} {k:>9} {HI:>4} {str(best):>12} {'YES' if best==F(1,n) else 'no':>8}  {arg}")
