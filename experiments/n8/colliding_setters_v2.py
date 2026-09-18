"""v1: colliding disparities are 19.2% of the pack but 31.3% of setter events.  Before that is
read as a residue effect, kill the obvious confound.

CONFOUND: colliding means d = 8bg, so a colliding disparity is >= 8g and skews LARGE.  If large
disparities set more often for a size reason, v1's signal is forced by size and says nothing about
residues.

Control: compare colliding vs non-colliding AT THE SAME SIZE RANK within the subject's own
disparity set.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
from collections import defaultdict
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def run(ds):
    t=TH/min(ds); n=0; setters=[]
    while n<4000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return n,setters
        t,s=max((nextOp(d,t),d) for d in b); setters.append(s); n+=1
    return None,None
rng=random.Random(1234)
# rank -> [colliding: (setter_events, opportunities)], [non-colliding: same]
tab=defaultdict(lambda: [[0,0],[0,0]])
for _ in range(2500):
    v=speeds(rng.sample(range(1,90),8))
    g=gcd_all(v)
    for i in range(8):
        ds=sorted(F(abs(v[j]-v[i])) for j in range(8) if j!=i)
        col={d for d in ds if (int(d)//g)%8==0}
        if not col: continue
        n,setters=run(ds)
        if n is None or n==0: continue
        for r,d in enumerate(ds):
            k=0 if d in col else 1
            tab[r][k][0]+=sum(1 for s in setters if s==d)
            tab[r][k][1]+=len(setters)
print("  setter rate by SIZE RANK within the subject's disparity set")
print("  (rank 0 = d_min, rank 6 = d_max).  Rate = setter events / cascade moves.\n")
print(f"  {'rank':>4}  {'colliding rate':>16} {'n':>8}   {'non-colliding rate':>19} {'n':>8}   ratio")
tc=tn=oc=on=0
for r in sorted(tab):
    c,nc=tab[r]
    rc = c[0]/c[1] if c[1] else float('nan')
    rn = nc[0]/nc[1] if nc[1] else float('nan')
    ratio = rc/rn if (nc[1] and rn>0) else float('nan')
    print(f"  {r:>4}  {rc:>16.4f} {c[1]:>8}   {rn:>19.4f} {nc[1]:>8}   {ratio:>5.2f}")
    tc+=c[0]; oc+=c[1]; tn+=nc[0]; on+=nc[1]
print(f"\n  pooled: colliding {tc/oc:.4f}   non-colliding {tn/on:.4f}   ratio {(tc/oc)/(tn/on):.2f}")
print("\n  If the ratio is ~1 at every rank, v1's signal was SIZE, not residue.")
