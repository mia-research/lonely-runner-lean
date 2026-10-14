"""Set out the examples and look at the one invariant: the READING PROFILE.

Everything is scale-invariant, so the object is the profile normalised somehow.  Normalise the
LARGEST reading to 8 (the band edge it sits just below) and compare the deep cases.
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
    while n<40000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n
        t=max(nextOp(d,t) for d in b); n+=1
    return None
def prof8(ds):
    """readings normalised so the LARGEST is exactly 8"""
    m=max(ds); return [float(F(d)*8/F(m)) for d in sorted(ds)]
KNOWN=[
 ([30,74,96,127,159,175,224], "verified 23-move"),
 ([28,69,95,123,154,172,220], "banded search"),
 ([55,131,181,233,293,329,419], "banded search"),
]
print("  KNOWN DEEP CASES, readings normalised so max = 8\n")
print(f"  {'depth':>5}  " + "".join(f"{i:>7}" for i in range(7)) + "   source")
for ds,src in KNOWN:
    p=prof8(ds)
    print(f"  {depth(ds):>5}  " + "".join(f"{x:>7.3f}" for x in p) + f"   {src}")

print("\n  harvesting more depth >= 18 cases by banded search...")
rng=random.Random(2718)
found=[]
tries=0
while len(found)<14 and tries<300000:
    tries+=1
    c=rng.randrange(20,70)
    xs=sorted(rng.sample(range(c+1,int(7.95*c)),6))
    ds=[c]+xs
    if len(set(ds))!=7: continue
    if not (7 < max(ds)/min(ds) < 8): continue
    d=depth(ds)
    if d is not None and d>=18: found.append((d,tuple(sorted(ds))))
found.sort(reverse=True)
print(f"  ({tries} candidates examined)\n")
print(f"  {'depth':>5}  " + "".join(f"{i:>7}" for i in range(7)))
for d,ds in found:
    print(f"  {d:>5}  " + "".join(f"{x:>7.3f}" for x in prof8(list(ds))))
allp=[prof8(ds) for ds,_ in KNOWN]+[prof8(list(ds)) for _,ds in found]
print(f"\n  mean profile over {len(allp)} deep cases:")
print("         " + "".join(f"{st.mean(p[i] for p in allp):>7.3f}" for i in range(7)))
print("  stdev  " + "".join(f"{st.pstdev([p[i] for p in allp]):>7.3f}" for i in range(7)))
print("\n  for contrast, mean profile of 400 SHALLOW (depth 0) cases in the same band:")
sh=[]
rng2=random.Random(99)
while len(sh)<400:
    c=rng2.randrange(20,70); xs=sorted(rng2.sample(range(c+1,int(7.95*c)),6)); ds=[c]+xs
    if len(set(ds))!=7 or not (7<max(ds)/min(ds)<8): continue
    if depth(ds)==0: sh.append(prof8(ds))
print("         " + "".join(f"{st.mean(p[i] for p in sh):>7.3f}" for i in range(7)))
print("  stdev  " + "".join(f"{st.pstdev([p[i] for p in sh]):>7.3f}" for i in range(7)))
