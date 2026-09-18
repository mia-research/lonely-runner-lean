"""The spike at c=30 sits between primes 29 and 31, and 30 = 2.3.5 shares factors with five of the
six other disparities.  Every input feature tested in orbit_law_v2 was a MAGNITUDE (Sigma, S,
spread_ratio, blocker count).  None was ARITHMETIC.  Test arithmetic features.

Guards, from this session's own record:
  * compute the forced floor / null before interpreting,
  * control the confound (here: magnitude) before believing.
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
print("=== on the scan where the spike lives ===")
print(f"  {'c':>4} {'depth':>6} {'sum gcd(c,a)':>13} {'max gcd':>8} {'#sharing':>9}")
for c in range(25,36):
    if c in REST: continue
    d=depth([c]+REST); gs=[gcd(c,a) for a in REST]
    print(f"  {c:>4} {str(d):>6} {sum(gs):>13} {max(gs):>8} {sum(1 for g in gs if g>1):>9}")

print("\n=== broadly: do arithmetic features predict depth? ===")
rng=random.Random(4711); rows=[]
for _ in range(3000):
    v=speeds(rng.sample(range(1,90),8))
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        n=depth(ds)
        if n is None: continue
        c=min(ds); others=[a for a in ds if a!=c] or [c]
        gs=[gcd(c,a) for a in others]
        pair=[gcd(a,b) for a,b in combinations(ds,2)]
        rows.append(dict(depth=n,
                         sum_gcd_min=sum(gs), max_gcd_min=max(gs),
                         n_share_min=sum(1 for g in gs if g>1),
                         sum_pair_gcd=sum(pair), max_pair_gcd=max(pair),
                         Sigma=float(sum(F(a,c) for a in ds)), S=float(F(max(ds),c))))
ys=[r['depth'] for r in rows]; my=st.mean(ys); sy=st.pstdev(ys)
print(f"  n = {len(rows)}   mean depth {my:.3f}")
for k in ('sum_gcd_min','max_gcd_min','n_share_min','sum_pair_gcd','max_pair_gcd','Sigma','S'):
    xs=[float(r[k]) for r in rows]; mx=st.mean(xs)
    c_=sum((a-mx)*(b-my) for a,b in zip(xs,ys))/len(xs)/(st.pstdev(xs)*sy)
    print(f"    {k:<14} correlation {c_:+.4f}")
print("\n  conditional means of depth by max gcd(d_min, other):")
for g in range(1,9):
    sub=[r['depth'] for r in rows if r['max_gcd_min']==g]
    if len(sub)>=40: print(f"    max gcd = {g:>2}: n={len(sub):>5}  mean depth {st.mean(sub):.3f}")
