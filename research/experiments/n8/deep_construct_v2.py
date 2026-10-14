"""Can deep cases be CONSTRUCTED rather than searched for?

Two clues: depth concentrates in S just above 7, and depth ~ (R-1).Sigma/8 with Sigma the sum of
readings.  With S pinned near 7.5, Sigma is maximised by pushing every disparity HIGH -- clustering
them near d_max instead of spreading them.  Baseline for comparison has Sigma = 29.5 and depth 23.

  A  all-high    : d_min, then six disparities packed just under 7.5 d_min   (max Sigma ~ 43)
  B  AP-spread   : readings an arithmetic progression from 1 to 7.5          (Sigma ~ 29.5, like baseline)
  C  random in-band control                                                   (matched S)
All speeds positive.  Reported against the adversarial record (23) so construction is judged, not
just described."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from math import floor
import random, statistics as st
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def depth(ds):
    ds=[F(d) for d in ds]
    if min(ds)<=0 or len(set(ds))!=len(ds): return None
    t=TH/min(ds); n=0
    while n<40000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n
        t=max(nextOp(d,t) for d in b); n+=1
    return None
def sigma(ds): return float(sum(F(d,min(ds)) for d in ds))
BASE=[30,74,96,127,159,175,224]
print(f"  baseline {BASE}: depth {depth(BASE)}  Sigma {sigma(BASE):.2f}  S {max(BASE)/min(BASE):.3f}\n")

def best(gen, N, label):
    b=(0,None)
    for _ in range(N):
        ds=gen()
        if ds is None: continue
        d=depth(ds)
        if d is not None and d>b[0]: b=(d,ds)
    ds=b[1]
    print(f"  {label:<24} best depth {b[0]:>3}   Sigma {sigma(ds):.2f}  S {max(ds)/min(ds):.3f}   {ds}")
    return b

rng=random.Random(31415)
def genA():                                  # all-high: pack six just under 7.5 c
    c=rng.randrange(20,140)
    hi=int(7.45*c)
    xs=sorted(rng.sample(range(int(6.6*c), hi+1), 6))
    ds=[c]+xs
    return ds if len(set(ds))==7 else None
def genB():                                  # AP-spread readings 1 .. 7.45
    c=rng.randrange(20,140)
    ds=[c]+[int(round(c*(1+6.45*k/6))) for k in range(1,7)]
    return ds if len(set(ds))==7 and min(ds)==c else None
def genC():                                  # random, S matched to (7,8)
    c=rng.randrange(20,140)
    xs=sorted(rng.sample(range(c+1, int(7.9*c)), 6))
    ds=[c]+xs
    return ds if max(ds)/c>7 else None
A=best(genA, 40000, "A all-high (max Sigma)")
B=best(genB, 40000, "B AP-spread readings")
C=best(genC, 40000, "C random in-band")
print()
print(f"  adversarial record on file: 23 (23-move case), 28 (the (27,70,...,393) case)")
for lab,r in (("A",A),("B",B),("C",C)):
    print(f"    strategy {lab}: {'BEATS' if r[0]>23 else 'matches' if r[0]==23 else 'below'} the 23-move record ({r[0]})")
