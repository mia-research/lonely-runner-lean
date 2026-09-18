"""Set out every VERIFIED deep case and compare reading profiles.
Normalise so the largest reading is 8 (the band edge it sits under).  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor
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
v=speeds((27,70,107,137,159,188,344,393))
C28=sorted(abs(v[j]-393) for j in range(8) if v[j]!=393)
CASES=[
 (sorted([30,74,96,127,159,175,224]), "23  parallel session, verified"),
 (C28,                                 "28  MANUSCRIPT v10 sec 6.7, verified"),
 (sorted([28,69,95,123,154,172,220]),  "27  banded climb"),
 (sorted([55,131,181,233,293,329,419]),"27  banded climb"),
]
print("  reading profiles, normalised so the LARGEST reading = 8\n")
print(f"  {'depth':>5} {'d_min':>6} {'S':>7}  " + "".join(f"{i:>7}" for i in range(7)) + "   source")
for ds,src in CASES:
    d=depth(ds); m=max(ds)
    p=[float(F(x)*8/F(m)) for x in ds]
    print(f"  {d:>5} {min(ds):>6} {m/min(ds):>7.3f}  " + "".join(f"{x:>7.3f}" for x in p) + f"   {src}")
print()
print("  raw disparities:")
for ds,src in CASES:
    print(f"    depth {depth(ds):>2}: {ds}")
print()
print("  GAPS between consecutive readings (normalised, max=8):")
for ds,src in CASES:
    m=max(ds); p=[float(F(x)*8/F(m)) for x in ds]
    g=[p[i+1]-p[i] for i in range(6)]
    print(f"    depth {depth(ds):>2}: " + "".join(f"{x:>7.3f}" for x in g))
