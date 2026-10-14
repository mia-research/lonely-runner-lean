"""Owner: "they don't change if you retest them... alter parameters to see what changes when and
by what degree."

Correlations over a random sample were the wrong tool.  The deep cases are FIXED objects.  So take
them and perturb one coordinate at a time, mapping the response surface of depth.

Baseline: the 23-move case, subject 1 of (1,31,75,97,128,160,176,225), disparities
{30,74,96,127,159,175,224}.  Perturbing one disparity = moving one runner, from this subject's view.

Controls included: global scaling (readings unchanged -> depth must be invariant).
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from fractions import Fraction as F
from math import floor, gcd
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
    while n<8000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n
        t=max(nextOp(d,t) for d in b); n+=1
    return None
BASE=[30,74,96,127,159,175,224]
print(f"  baseline disparities {BASE}   depth = {depth(BASE)}\n")
print("  CONTROL -- global scaling (readings unchanged):")
for k in (1,2,3,5,7):
    print(f"    x{k}: {[k*d for d in BASE]}  depth {depth([k*d for d in BASE])}")
print()
print("  ONE-AT-A-TIME response.  Row = which disparity moves; columns = delta.")
deltas=list(range(-6,7))
print(f"    {'d':>5} | " + " ".join(f"{x:>4}" for x in deltas))
print("    " + "-"*(7+5*len(deltas)))
for idx,d0 in enumerate(BASE):
    row=[]
    for dl in deltas:
        ds=list(BASE); ds[idx]=d0+dl
        r=depth(ds)
        row.append("  ." if dl==0 else (f"{r:>4}" if r is not None else "   x"))
    print(f"    {d0:>5} | " + " ".join(row) + f"     (baseline {depth(BASE)})")
print("\n    '.' = baseline position, 'x' = invalid (duplicate or non-positive)")
