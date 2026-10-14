"""Sharpen R analytically.

At the final scale every reading is s_i.R (s_i = d_i/d_min), so clearance means all seven
s_i.R mod 8 lie in [1,7].  The cascade walks forward from R = 1, so

    R_final = min { R >= 1 : for all i, s_i.R mod 8 in [1,7] }

If true, R is computable from the PROFILE directly -- no cascade needed -- and the bad set of
disparity s is the union of [(8k-1)/s, (8k+1)/s], so the first clear point is found by sweeping
interval endpoints.  Verify against the cascade, then use it to search.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor
import random
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def R_cascade(ds):
    ds=[F(d) for d in ds]
    if min(ds)<=0 or len(set(ds))!=len(ds): return None
    c=min(ds); t=TH/c; n=0
    while n<200000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return c*8*t
        t=max(nextOp(d,t) for d in b); n+=1
    return None
def R_direct(ds, RMAX=200):
    """smallest R >= 1 with every s_i.R mod 8 in [1,7], by sweeping bad-interval right endpoints"""
    c=F(min(ds)); S=[F(d)/c for d in ds]
    cands=[F(1)]
    for s in S:
        k=1
        while True:
            r=F(8*k+1)/s
            if r>RMAX: break
            if r>=1: cands.append(r)
            k+=1
    cands=sorted(set(cands))
    for R in cands:
        if all(1 <= (s*R) % 8 <= 7 for s in S): return R
    return None
print("  verifying R_direct == R_cascade")
rng=random.Random(31337); ok=0; tot=0; bad=[]
for _ in range(1500):
    v=speeds(rng.sample(range(1,90),8))
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        a=R_cascade(ds); b=R_direct(ds)
        if a is None or b is None: continue
        tot+=1
        if a==b: ok+=1
        elif len(bad)<3: bad.append((ds,float(a),float(b)))
print(f"    {ok}/{tot} agree")
for ds,a,b in bad: print(f"      mismatch {ds}: cascade {a:.6f}  direct {b:.6f}")
KNOWN=[[30,74,96,127,159,175,224],[49,205,234,256,286,323,366],
       [46,107,146,194,241,268,344],[158,367,505,664,827,918,1179]]
print("\n  on the known deep cases:")
for ds in KNOWN:
    a=R_cascade(ds); b=R_direct(ds)
    print(f"    {ds}: cascade R = {float(a):.6f}  direct R = {float(b):.6f}  {'OK' if a==b else 'MISMATCH'}")
