"""v1: depth is piecewise constant with sharp thresholds; 30 -> 32 drops depth 23 -> 0.
That transition is the S <= 7 boundary (224/32 = 7 exactly).  So the CLAIM is:

    depth changes exactly where a reading crosses a band boundary -- i.e. where the set of
    INITIAL BLOCKERS changes -- and is constant between such crossings.

Test it by scanning d_min finely and annotating, at each value, which disparities are initial
blockers (by clear_iff: a mod 8c outside [c, 7c]).  If the claim holds, depth is constant exactly
on the intervals where the blocker set is constant.
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
    while n<8000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n
        t=max(nextOp(d,t) for d in b); n+=1
    return None
REST=[74,96,127,159,175,224]
print("  scanning d_min, the other six disparities fixed at", REST, "\n")
print(f"  {'c':>4} {'depth':>6}  {'initial blockers (a, reading a/c)':<44} {'blocker set changed?'}")
print("  " + "-"*84)
prev=None
for c in range(20,46):
    ds=[c]+REST
    if c in REST: continue
    d=depth(ds)
    blk=[a for a in ds if not (c <= a%(8*c) <= 7*c)]
    desc=", ".join(f"{a}({float(F(a,c)):.2f})" for a in blk) or "none"
    changed = "" if blk==prev else "  <-- CHANGED"
    print(f"  {c:>4} {str(d):>6}  {desc:<44}{changed}")
    prev=blk
print()
print("  Reading the boundaries: 224/c crosses 7 at c = 32, and 224/c crosses 8 at c = 28.")
print("  For c in [28,32) the reading is in (7,8) -- the pure-spread bad band -- and 224 blocks.")
print("  At c >= 32 every reading is <= 7 and clear_of_reading_le_seven forces depth 0.")
