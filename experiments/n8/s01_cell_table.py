"""S01: verify the 13-cell representative table for the four UNIT runners at
representative speeds rho in {1,3,5,7}, exact rational arithmetic."""
from fractions import Fraction as F
from n8_fibre_core import bad

# breakpoints of floor(rho*x) for rho in 1,3,5,7 inside [1/8,7/8]
pts = {F(1,8), F(7,8)}
for rho in (1,3,5,7):
    for j in range(0, rho+1):
        p = F(j, rho)
        if F(1,8) <= p <= F(7,8):
            pts.add(p)
pts = sorted(pts)
print("breakpoints:", [str(p) for p in pts], "-> cells:", len(pts)-1)

rows=[]
for i in range(len(pts)-1):
    lo, hi = pts[i], pts[i+1]
    mid = (lo+hi)/2                      # exact rational interior point
    blk=set()
    ts={}
    for rho in (1,3,5,7):
        t = (rho*mid.numerator)//mid.denominator   # floor(rho*mid), exact
        ts[rho]=t
        blk |= bad(rho, t)
    unc = sorted(set(range(8))-blk)
    par = "empty" if not unc else ("odd" if all(u%2 for u in unc) else ("even" if all(u%2==0 for u in unc) else "MIXED"))
    rows.append((lo,hi,ts,unc,par))
    print(f"x in [{lo}, {hi})  t=(1:{ts[1]},3:{ts[3]},5:{ts[5]},7:{ts[7]})  uncovered={unc}  {par}")

print()
mixed=[(str(lo),str(hi),unc) for lo,hi,ts,unc,par in rows if par=="MIXED"]
print("MIXED-parity (both a unit and a non-unit uncovered) cells:", mixed)
