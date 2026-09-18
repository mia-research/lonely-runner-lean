"""Cross-check the parallel session's perturbation analysis against measurements already made.

Their claims, testable:
 (1) "varying d_6 = 224 continuously across [223.80, 224.20] holds depth at exactly 23"
 (2) "d_0 = 30 holds depth 23 until the exact wall at 29.875 = 239/8"
     -- I bisected that wall to 1225/41 = 29.878049.  239/8 is also not of the band-edge form
        e(8M+-1)/(8N+1), since 8 is not 8N+-1.
 (3) "224 -> 225 breaks its colliding status (8|224, 8 not| 225), eliminating its blockings at
      steps 0,4,10,13 simultaneously, collapsing 23 to 1"
     -- causal claim: test whether colliding status is what matters.
 (4) their setter census: 224 sets 4, 175 sets 4, 159 sets 4, 127 sets 4, 96 sets 3, 74 sets 3,
     30 sets 1.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from math import floor
from collections import Counter
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
    while n<200000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n
        t=max(nextOp(d,t) for d in b); n+=1
    return None
def setters(ds):
    ds=[F(d) for d in ds]; t=TH/min(ds); seq=[]
    for _ in range(200000):
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return seq
        t,s=max((nextOp(d,t),d) for d in b); seq.append(int(s))
    return seq
A=[30,74,96,127,159,175,224]
print("(1) d_6 = 224 varied over [223.80, 224.20] -- do all give depth 23?")
vals=[]
for k in range(22380,22421):
    ds=A[:6]+[F(k,100)]
    vals.append((F(k,100), depth(sorted(ds))))
bad=[(x,d) for x,d in vals if d!=23]
print(f"    {len(vals)} points; depth 23 at {sum(1 for _,d in vals if d==23)}; others: "
      f"{[(float(x),d) for x,d in bad][:6]}{' ...' if len(bad)>6 else ''}")
print(f"    -> claim {'CONFIRMED' if not bad else 'FALSE'}\n")

print("(2) the wall below d_0 = 30: their 239/8 = 29.875 vs my 1225/41 = 29.878049")
for c in (F(239,8), F(1225,41)):
    lo=depth(sorted([c-F(1,100000)]+A[1:]))
    hi=depth(sorted([c+F(1,100000)]+A[1:]))
    print(f"    c = {c} = {float(c):.6f}:  just below {lo}, just above {hi}   "
          f"{'IS a wall' if lo!=hi else 'NOT a wall'}")
print(f"    depth exactly at 29.875: {depth(sorted([F(239,8)]+A[1:]))}")
print(f"    depth exactly at 29.90 : {depth(sorted([F(299,10)]+A[1:]))}\n")

print("(3) is the collapse at 224 -> 225 caused by LOSING COLLIDING STATUS (8 | d)?")
print(f"    {'d_6':>5} {'8 | d?':>7} {'depth':>6}")
for x in (216,218,220,221,222,223,224,225,226,228,230,232,240):
    ds=sorted(A[:6]+[x])
    print(f"    {x:>5} {str(x%8==0):>7} {str(depth(ds)):>6}")
print("    -> if non-colliding values also give depth 23, the causal claim fails\n")

print("(4) setter census on the 23-move case:")
c=Counter(setters(A))
print(f"    {dict(sorted(c.items()))}   total {sum(c.values())}")
print(f"    their claim: 224:4, 175:4, 159:4, 127:4, 96:3, 74:3, 30:1")
theirs={224:4,175:4,159:4,127:4,96:3,74:3,30:1}
print(f"    -> {'MATCHES' if dict(c)==theirs else 'differs'}")
