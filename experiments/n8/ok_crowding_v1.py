#!/usr/bin/env python3
"""The GECT isolation-crowding duality (audit C15), transported to n=8.

C15 confirmed three of four exactly: L peaks at isolation, C at non-coprime times,
l_i*c_i = 0 identically; conservation FAILS and S = L+C is an order parameter (0 at
coprime r, 1 at collapse).  Transport the one-sided form to our object and see what
survives as an EXACT statement.

  c_j(t) = max(0, 1 - 8||e_j t||)     crowding of runner j against the stationary one
  l_j(t) = max(0, 8||e_j t|| - 1)     loneliness
  LRC(8) for E  <=>  exists t with C(t) = sum_j c_j(t) = 0.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd
import random

def nrm(x):
    x=x-int(x)
    if x<0: x+=1
    return min(x,1-x)

# exact integral of c_j and of l_j+c_j over one period, by breakpoints
def integ(e, which):
    tot=F(0); D=8*e
    pts=sorted({F(k,D) for k in range(D+1)})
    for a,b in zip(pts,pts[1:]):
        m=(a+b)/2; v=8*nrm(e*m)
        f = max(F(0),1-v) if which=='c' else abs(v-1)
        # f is linear on the cell; use midpoint (exact for linear)
        tot += f*(b-a)
    return tot

print("EXACT: is the crowding integral an invariant of the speed?")
for e in (1,2,3,5,7,8,12,13,14):
    print(f"  e={e:>3}   int c = {integ(e,'c')}   int (l+c) = {integ(e,'lc')}")

print("\nSo for any 7-tuple: int C = 7 * 1/8 = 7/8, int S = 7 * 5/4 = 35/4 -- speed-free.")
print("l_j * c_j = 0 identically: ", end="")
random.seed(1)
ok=all(max(F(0),1-8*nrm(F(e)*F(random.randint(1,997),997)))*
       max(F(0),8*nrm(F(e)*F(random.randint(1,997),997))-1)==0
       for e in range(1,40) for _ in range(20))
print(ok)

print("\nWHERE IT LANDS: int C = 7/8 is exactly the first moment.")
print("  measure of the good set >= 1 - int C / (value of c on a bad point)")
print("  c <= 1, so Markov gives |{C>0}| <= 7/8 ... only if c were an indicator.")
print("  It is not: c is a tent, so |{C>0}| = |union B_j| and sum|B_j| = 7*(1/4) = 7/4 > 1.")
print("  The tent-weighted mean 7/8 < 1 and the indicator mean 7/4 > 1 are the SAME")
print("  first moment read two ways; neither separates. Checked:")
for E in ((1,2,3,4,5,6,7),(2,6,7,8,10,13,14),(1,4,5,6,7,11,13)):
    D=8*reduce(lambda a,b:a*b//gcd(a,b),E)
    pts=sorted({F(k,D) for k in range(D+1)})
    ic=F(0); bad=F(0)
    for a,b in zip(pts,pts[1:]):
        m=(a+b)/2
        cs=sum(max(F(0),1-8*nrm(e*m)) for e in E)
        ic+=cs*(b-a)
        if cs>0: bad+=b-a
    print(f"  E={E}  int C = {ic} (= 7/8: {ic==F(7,8)})   |{{C>0}}| = {bad} = {float(bad):.6f}")
