"""We have not found the cause.  Perturb something not yet perturbed: RESOLUTION.

Depth is scale-invariant (verified), so scaling the baseline by 10 and stepping the minimum by 1
gives a 10x finer view of the SAME function.  Question: is the c=30 spike isolated, or is depth a
wild arithmetic function with spikes at every resolution?

Baseline x10: {300, 740, 960, 1270, 1590, 1750, 2240}; scan the minimum 250..340 (= 25.0..34.0).
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
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
REST=[740,960,1270,1590,1750,2240]
print("  minimum scanned at 0.1 resolution (baseline x10).  '#' marks depth >= 20.\n")
vals=[]
for c in range(250,341):
    d=depth([c]+REST)
    vals.append((c/10.0, d))
# print as a compact strip
line=""
for c10,d in vals:
    line += "#" if (d is not None and d>=20) else ("+" if (d is not None and d>=10) else ".")
print("   25.0" + " "*(len(line)-12) + "34.0")
print("   " + line)
print()
print("  peaks (depth >= 15):")
for c10,d in vals:
    if d is not None and d>=15: print(f"    c = {c10:>5}  depth {d}")
print()
import statistics as st
ds=[d for _,d in vals if d is not None]
print(f"  over the scan: n={len(ds)}  mean {st.mean(ds):.2f}  median {st.median(ds)}  max {max(ds)}")
print(f"  distinct depth values: {sorted(set(ds))}")
