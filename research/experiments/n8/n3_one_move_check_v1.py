# Exact check of the hand proof of order 3: disparities a<b; the cascade from t0=1/(3a) is fixed at t0 or after one move.
from fractions import Fraction as F
import math
def dist(x): x-=math.floor(x); return min(x,1-x)
bad=0; moved=0; tot=0
for a in range(1,121):
    for b in range(a+1,241):
        tot+=1
        t0=F(1,3*a)
        if dist(b*t0)>=F(1,3): continue
        moved+=1
        N=math.floor(F(b,3*a)+F(1,3))   # nearest integer lap
        t1=(N+F(1,3))/b
        ok = dist(b*t1)>=F(1,3) and dist(a*t1)>=F(1,3) and (b*t0)<=N+F(1,3)
        if not ok: bad+=1
print(tot,moved,bad)
