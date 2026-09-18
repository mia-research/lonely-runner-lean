"""v1: depth ~ (R-1).Sigma/8 with overlap factor ~1.37, correlation 0.86.  But R is an OUTPUT.
So: which INPUT-only features predict depth, and does S bound it?

Sigma = sum of readings d_i/d_min  <=  7S, so the v1 law predicts  depth <~ (R-1).7S/8 -- LINEAR
in S if R is bounded.  Memory records k bounded given S (6 at S<=20, 7 at S<=30, 146 at S<=1000),
which is consistent.  Test the linearity directly, and rank input features by correlation.
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random, statistics as st
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def cascade(ds):
    t=TH/min(ds); n=0
    while n<8000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return t,n
        t=max(nextOp(d,t) for d in b); n+=1
    return None,None
def feats(ds):
    dmin=min(ds); s=[d/dmin for d in ds]
    return dict(
        Sigma=float(sum(s)),
        S=float(max(s)),
        n_block0=sum(1 for x in s if circd(x/8)<F(1,8)),
        spread_ratio=float(sum(s)/max(s)),
    )
print("=== does max depth grow linearly in S? ===")
rng=random.Random(2024)
print(f"  {'S cap':>7} {'n':>7} {'max depth':>10} {'mean depth':>11} {'max R':>9}")
for cap in (8,10,15,20,30,50,100,300):
    md=0; ds_all=[]; mr=0; cnt=0
    tries=0
    while cnt<2500 and tries<200000:
        tries+=1
        v=speeds(rng.sample(range(1,120),8))
        for i in range(8):
            ds=[F(abs(v[j]-v[i])) for j in range(8) if j!=i]
            dmin=min(ds)
            if max(ds)/dmin>cap: continue
            t,n=cascade(ds)
            if t is None: continue
            cnt+=1; md=max(md,n); ds_all.append(n); mr=max(mr,float(dmin*8*t))
    if ds_all:
        print(f"  {cap:>7} {cnt:>7} {md:>10} {st.mean(ds_all):>11.3f} {mr:>9.3f}")

print("\n=== input-only features vs depth (correlation, depth >= 1) ===")
rng=random.Random(99); rows=[]
for _ in range(2500):
    v=speeds(rng.sample(range(1,90),8))
    for i in range(8):
        ds=[F(abs(v[j]-v[i])) for j in range(8) if j!=i]
        t,n=cascade(ds)
        if t is None or n==0: continue
        f=feats(ds); f['depth']=n; rows.append(f)
ys=[r['depth'] for r in rows]; my=st.mean(ys); sy=st.pstdev(ys)
for k in ('Sigma','S','n_block0','spread_ratio'):
    xs=[r[k] for r in rows]; mx=st.mean(xs)
    c=sum((a-mx)*(b-my) for a,b in zip(xs,ys))/len(xs)/(st.pstdev(xs)*sy)
    print(f"  {k:<14} correlation with depth: {c:+.4f}")
print(f"  n = {len(rows)}")
