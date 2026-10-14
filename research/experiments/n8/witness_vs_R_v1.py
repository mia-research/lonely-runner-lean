"""Owner: does the multiplier-frame witness work (t = lambda/(8M)) indicate where our witness is?

THE LINK IS EXACT.  R = 8.d_min.t, so a witness at t = lambda/(8M) has

        R  =  8.d_min.lambda/(8M)  =  d_min . lambda / M .

Since R is the FIRST clear instant, ANY clear instant bounds R above:  R <= d_min.lambda/M.
So the multiplier frame does give upper bounds on R.  The question is whether they are useful.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
import random, statistics as st
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def cascade_t(ds):
    ds=[F(d) for d in ds]; t=TH/min(ds); n=0
    while n<200000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return t
        t=max(nextOp(d,t) for d in b); n+=1
def mult_witness(ds, MCAP=400):
    """first (M, lambda) with t = lambda/(8M) clear -- the earlier witness-complexity search"""
    for M in range(1,MCAP+1):
        N=8*M
        for lam in range(1,N):
            t=F(lam,N)
            if all(circd(F(d)*t)>=TH for d in ds): return M,lam,t
    return None,None,None
def min_ratio_witness(ds, MCAP=60):
    """the clear (M, lambda) MINIMISING lambda/M -- i.e. minimising R"""
    best=None
    for M in range(1,MCAP+1):
        N=8*M
        for lam in range(1,N):
            if best and F(lam,M) >= best[0]: continue
            t=F(lam,N)
            if all(circd(F(d)*t)>=TH for d in ds): best=(F(lam,M),M,lam,t)
    return best
CASES=[("23-move",[30,74,96,127,159,175,224]),
       ("28-move",[49,205,234,256,286,323,366]),
       ("R=11.96",[2520,5750,8003,10557,13161,14580,18745])]
print(f"  {'case':>9} {'R (cascade)':>13} {'first-M witness':>18} {'its R bound':>13} {'ratio':>7}")
for nm,ds in CASES:
    t=cascade_t(ds); R=F(min(ds))*8*t
    M,lam,tm=mult_witness(ds)
    Rb=F(min(ds))*8*tm
    print(f"  {nm:>9} {float(R):>13.5f} {f'M={M}, lam={lam}':>18} {float(Rb):>13.5f} {float(Rb/R):>7.2f}x")
print()
print("  and the SAME frame asked to minimise lambda/M instead of M:")
for nm,ds in CASES[:2]:
    t=cascade_t(ds); R=F(min(ds))*8*t
    b=min_ratio_witness(ds)
    if b:
        ratio,M,lam,tm=b; Rb=F(min(ds))*8*tm
        print(f"  {nm:>9}: best lambda/M gives R = {float(Rb):.5f}  (cascade R = {float(R):.5f})  "
              f"{'MATCHES' if Rb==R else 'differs'}")
print()
print("  -> the multiplier frame bounds R above, but the FIRST-M witness is the wrong objective:")
print("     it minimises the DENOMINATOR, not the magnitude.  Minimising lambda/M instead just")
print("     recovers R itself, because R IS the minimum over clear instants.")
