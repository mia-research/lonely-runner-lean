"""Does the BS frame help produce WITNESSES?

BS's counting certifies that a search over U(Z_N) succeeds -- so it is a witness-production method,
not only an existence proof.  Compare the witnesses the two routes produce for the same subject:

  CASCADE   : t = (8k+1)/(8d) for some disparity d -- denominator 8d, depth = number of moves.
  MULTIPLIER: t = lambda/(8M) -- the BS form.  Minimal M is the witness's complexity in that frame.

Both are rational instants, so the honest common currency is the DENOMINATOR of the witness.
Question: does the multiplier frame find lower-complexity witnesses than the cascade, and is its M
bounded?  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
from collections import Counter
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def cascade(ds):
    m=min(ds); t=TH/m; n=0
    while n<4000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return t,n
        t=max(nextOp(d,t) for d in b); n+=1
    return None,None
def min_multiplier_M(ds,MCAP=400):
    """smallest M with some lambda making t = lambda/(8M) a witness"""
    for M in range(1,MCAP+1):
        N=8*M
        for lam in range(1,N):
            t=F(lam,N)
            if all(circd(F(d)*t)>=TH for d in ds): return M,lam
    return None,None
rng=random.Random(9090)
rows=[]
for _ in range(400):
    v=speeds(rng.sample(range(1,90),8))
    for i in range(8):
        ds=[F(abs(v[j]-v[i])) for j in range(8) if j!=i]
        t,dep=cascade(ds)
        if t is None: continue
        M,lam=min_multiplier_M(ds)
        if M is None: continue
        rows.append((t.denominator, dep, M, 8*M))
cd=[r[0] for r in rows]; dep=[r[1] for r in rows]; Ms=[r[2] for r in rows]; md=[r[3] for r in rows]
def stats(x,name):
    x=sorted(x); n=len(x)
    print(f"  {name:<28} min {x[0]:>6}  median {x[n//2]:>6}  p90 {x[int(n*.9)]:>6}  max {x[-1]:>6}")
print(f"  {len(rows)} subjects\n")
stats(cd,"cascade witness denominator")
stats(md,"multiplier witness denom (8M)")
stats(Ms,"minimal M")
stats(dep,"cascade depth (moves)")
lower=sum(1 for r in rows if r[3]<r[0]); eq=sum(1 for r in rows if r[3]==r[0])
print(f"\n  multiplier denominator STRICTLY LOWER than cascade's : {lower} of {len(rows)}  ({lower/len(rows):.4f})")
print(f"  equal                                                : {eq}  ({eq/len(rows):.4f})")
print(f"\n  minimal-M distribution (top 10): {Counter(Ms).most_common(10)}")
