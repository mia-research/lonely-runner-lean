"""Owner: permutations, shifts by magnitude or increment, on or near slots -- then CONSTRUCT.

Clue already in hand: both known deep cases sit JUST ABOVE the proved S <= 7 threshold.
  23-move: {30,74,96,127,159,175,224}  S = 224/30 = 7.47
  28-move: {43,106,163,216,270,313,366} S = 366/43 = 8.51
If depth concentrates in a narrow band above 7, that is constructible rather than searchable.

Three probes:
 (1) where does depth live as a function of S?   (narrow bands, max and mean)
 (2) increment shift: d_i + k for all i (NOT scale-invariant, unlike x k)
 (3) slot shift: move one disparity onto / off a multiple of 8.d_min
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
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
    while n<20000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n
        t=max(nextOp(d,t) for d in b); n+=1
    return None

print("=== (1) where does depth live, as a function of S? ===")
bands=[(7,7.25),(7.25,7.5),(7.5,8),(8,9),(9,10),(10,12),(12,16),(16,24),(24,40),(40,1e9)]
acc={b:[] for b in bands}
rng=random.Random(20260918)
for _ in range(60000):
    v=speeds(rng.sample(range(1,160),8))
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        S=max(ds)/min(ds)
        for b in bands:
            if b[0]<=S<b[1]:
                d=depth(ds)
                if d is not None: acc[b].append(d)
                break
print(f"  {'S band':>14} {'n':>7} {'mean':>7} {'max':>5} {'P(depth>=5)':>12}")
for b in bands:
    a=acc[b]
    if len(a)<50: continue
    print(f"  {str(b):>14} {len(a):>7} {st.mean(a):>7.3f} {max(a):>5} {sum(1 for x in a if x>=5)/len(a):>12.4f}")

print("\n=== (2) increment shift on the 23-move case: d_i + k for all i ===")
BASE=[30,74,96,127,159,175,224]
print(f"  {'k':>4} {'depth':>6} {'S':>7}")
for k in list(range(-10,11)):
    ds=[d+k for d in BASE]
    if min(ds)<=0: continue
    print(f"  {k:>4} {str(depth(ds)):>6} {max(ds)/min(ds):>7.3f}")
