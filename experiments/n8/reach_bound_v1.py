"""The reach bound, and a refinement that uses the comb count.

REACH LEMMA.  If x lies in a bad interval of comb s at level m, then s.x > 8m-1, so that interval's
right endpoint is (8m+1)/s < x.(8m+1)/(8m-1).  Each step multiplies the reach by at most
(8m+1)/(8m-1), maximal 9/7 at m = 1.

REFINEMENT.  Comb i has exactly ONE interval at each level m.  With six combs, at most 6 steps can
be at m = 1, contributing at most (9/7)^6; at most 6 more at m = 2, contributing (17/15)^6; and so
on.  So the reach after using levels 1..M across all combs is at most

        prod_{m=1..M} ((8m+1)/(8m-1))^6

and a chain reaching R needs at least as many steps as that product requires.  This is a LOWER bound
on the number of moves, sharper than log R / log(9/7).

Test it against the known cascades."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from math import floor, log
NC=6
def naive_bound(R):
    return int(-(-log(R)/log(9/7)//1))
def refined_bound(R):
    """greedy: spend steps at the cheapest level first (largest multiplier), 6 per level"""
    reach=1.0; steps=0; m=1
    while reach < R and m < 500:
        mult=(8*m+1)/(8*m-1)
        for _ in range(NC):
            if reach>=R: break
            reach*=mult; steps+=1
        m+=1
    return steps
def depth_and_R(ds):
    TH=F(1,8)
    def circd(x): x=x-floor(x); return min(x,1-x)
    def nextOp(d,t):
        k=floor(d*t-TH)
        while F(k)+TH<d*t: k+=1
        if k<0: k=0
        return (F(k)+TH)/d
    ds=[F(d) for d in ds]; c=min(ds); t=TH/c; n=0
    while n<200000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n, float(c*8*t)
        t=max(nextOp(d,t) for d in b); n+=1
CASES=[("23-move",[30,74,96,127,159,175,224]),("28-move",[49,205,234,256,286,323,366]),
       ("27 banded",[28,69,95,123,154,172,220]),("R=11.93",[158,367,505,664,827,918,1179]),
       ("R=11.96",[2520,5750,8003,10557,13161,14580,18745])]
print(f"  {'case':>10} {'depth':>6} {'R':>9} {'naive >= ':>10} {'refined >= ':>12}  refined valid?")
ok=True
for nm,ds in CASES:
    K,R=depth_and_R(ds)
    nb=naive_bound(R); rb=refined_bound(R)
    v = rb<=K
    ok &= v
    print(f"  {nm:>10} {K:>6} {R:>9.4f} {nb:>10} {rb:>12}  {'ok' if v else 'VIOLATED'}")
print(f"\n  refined bound valid on all cases: {ok}")
print()
print(f"  what the refined bound says for the band boundaries:")
for R in (7.0, 9.0, 15.0, 16.0, 17.0, 23.0):
    print(f"    reaching R = {R:>5}: naive >= {naive_bound(R):>3} steps, refined >= {refined_bound(R):>3} steps")
print()
print("  and the ceiling the product allows, level by level (six combs per level):")
reach=1.0
for m in range(1,9):
    reach *= ((8*m+1)/(8*m-1))**NC
    print(f"    through level m = {m}: reach <= {reach:.4f}  ({6*m} steps)")
print("  -> the product diverges, so this bounds the number of steps from BELOW and never")
print("     forbids reaching any R.  It is a lower bound on depth, not a bound on R.")
