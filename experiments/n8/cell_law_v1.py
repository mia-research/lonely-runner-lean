"""The fitted law: cell width x 0.839 per unit of depth, i.e. width ~ 1.192^(-depth).

MECHANISM HYPOTHESIS: each cascade step contracts the scale by lambda, so a cell needing one more
step is the pre-image of a cell under one more contraction -- roughly lambda times narrower.  That
predicts the decay base equals the TYPICAL DILATION.  Test: compute the geometric mean of lambda
over cascade steps and compare it to 1.192.

If they agree, the width law is explained, not fitted.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, log, exp
import random, statistics as st
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def lams(ds):
    ds=[F(d) for d in ds]; t=TH/min(ds); out=[]
    for _ in range(40000):
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return out
        tn=max(nextOp(d,t) for d in b)
        out.append(float(tn/t)); t=tn
    return out
print("=== dilation statistics ===")
rng=random.Random(5150); alll=[]; bycase={}
for _ in range(4000):
    v=speeds(rng.sample(range(1,90),8))
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        L=lams(ds)
        if L: alll+=L
print(f"  {len(alll)} dilation steps sampled")
print(f"    arithmetic mean lambda : {st.mean(alll):.5f}")
gm=exp(st.mean(log(x) for x in alll))
print(f"    GEOMETRIC mean lambda  : {gm:.5f}")
print(f"    median                 : {st.median(alll):.5f}")
print(f"\n  fitted decay base from the cell census : 1.19178   (= 1/0.8391)")
print(f"  geometric mean dilation                : {gm:.5f}")
print(f"  agreement: {'YES' if abs(gm-1.19178)/1.19178 < 0.12 else 'NO'}  "
      f"(relative difference {abs(gm-1.19178)/1.19178:.3f})")
print("\n  on the two known deep cases specifically:")
for name,ds in (("23-move",[30,74,96,127,159,175,224]),("28-move",[43,106,163,216,270,313,366])):
    L=lams(ds)
    if L:
        g=exp(st.mean(log(x) for x in L))
        print(f"    {name}: {len(L)} steps, geometric mean lambda = {g:.5f}, total R = {exp(sum(log(x) for x in L)):.4f}")
