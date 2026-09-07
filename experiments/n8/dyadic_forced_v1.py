"""
Is the "0 unsettled" figure of dyadic_depth_v1 FORCED?  Runnable artifact, not a
judgment.  Exact rational/integer arithmetic.

The suspicion: kappa(T) < infinity is not evidence for anything, because
  * if M(T) > 1/8 then  g(t) = min_v ||v t||  is continuous and exceeds 1/8 at some
    point, hence exceeds 1/8 on an open interval; the dyadics are dense, so a dyadic
    witness EXISTS for every such T, with no input from the 2-adic structure at all;
  * LRC(8) (Rosenfeld 2025) gives M(T) >= 1/8 for every T;
  * the only T left are the tight ones, M(T) = 1/8, and their witness set was
    computed to be {1/8,3/8,5/8,7/8} -- already dyadic.
If that is right then (a) no T can ever come out unsettled, so the null is forced,
and (b) kappa must track  log2(1/w)  where w is the width of the widest good
interval -- i.e. the "2-adic depth" is just the resolution needed to land in a gap,
carrying no arithmetic content.

TEST: for sampled residual sets, measure w exactly and compare kappa to
ceil(log2(1/w)).  If kappa is pinned by w, the 2-adic reading is void.
"""
import random, sys
from math import gcd, log2, ceil
from fractions import Fraction as F
from itertools import combinations
sys.path.insert(0, 'experiments/n8')
from dyadic_depth_v1 import kappa, draw

def good_intervals(T, n=8):
    """Maximal closed intervals in [0,1] where min_v ||v t|| >= 1/n.  Exact."""
    iv=[]
    for v in T:
        w=F(1,n*v)
        for k in range(0,v+1):
            lo,hi=F(k,v)-w,F(k,v)+w
            if hi<=0 or lo>=1: continue
            iv.append((max(lo,F(0)),min(hi,F(1))))
    iv.sort()
    out,cur=[],F(0)
    for lo,hi in iv:
        if lo>cur: out.append((cur,lo))
        if hi>cur: cur=hi
    if cur<1: out.append((cur,F(1)))
    return out

rng=random.Random(31337)
print(f"{'V':>5} {'T':>34} {'kappa':>5} {'widest good interval w':>24} {'ceil(log2 1/w)':>15}")
agree=0; tot=0
for V in (50,100,200,400,800):
    for _ in range(6):
        T=draw(V,rng)
        k=kappa(T,16)
        gs=good_intervals(T)
        w=max((hi-lo for lo,hi in gs), default=F(0))
        b=ceil(log2(1/float(w))) if w>0 else None
        tot+=1; agree += (b is not None and abs(k-b)<=2)
        print(f"{V:>5} {str(T):>34} {k:>5} {str(w):>24} {b:>15}")
print(f"\nkappa within 2 of ceil(log2 1/w): {agree}/{tot}")
print("If that ratio is ~1, kappa measures the RESOLUTION needed to land in the")
print("widest good gap, not any 2-adic property of T: the finding is forced.")
