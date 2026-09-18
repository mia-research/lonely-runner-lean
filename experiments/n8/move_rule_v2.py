"""v1: argmin s/(8M+1) matched the cascade 18283/18286 -- three misses.  By construction it should
be exact, so the misses should be TIES where a different blocker is named but the SAME scale
results.  Check that, and characterise where the 'smallest M wins' shortcut (97.3%) fails.

Shortcut analysis: the ratio is (8M+delta)/(8M+1), increasing in M and in delta.  A larger M with
delta near -1 can beat a smaller M with delta near +1, e.g. (8.9)/9 = 0.9889 vs (15.1)/17 = 0.8882.
So the shortcut fails exactly when a later-lap blocker sits far enough BELOW its multiple.
All speeds positive."""
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
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
rng=random.Random(8642)
scale_eq=tot=0; ident_miss=0
fail_dM=Counter(); fail_delta=[]
for _ in range(2500):
    v=speeds(rng.sample(range(1,90),8))
    g=gcd_all(v)
    for i in range(8):
        dsr=sorted(abs(v[j]-v[i])//g for j in range(8) if j!=i)
        ds=[F(a*g) for a in dsr]
        e=min(dsr); N=0; t=TH/min(ds); n=0
        while n<60:
            b=[d for d in ds if circd(d*t)<TH]
            if not b: break
            tnew,setter=max((nextOp(d,t),d) for d in b)
            info=[]
            for d in b:
                a=int(d)//g; s=F(a*(8*N+1),e); M=round(s/8)
                info.append((F(s,8*M+1), M, s, a, d))
            best=min(info)
            tot+=1
            # does the derived rule give the same SCALE (not necessarily the same named blocker)?
            Dpred=(1/(8*t))*best[0]
            scale_eq += (Dpred == 1/(8*tnew))
            if best[4]!=setter: ident_miss+=1
            # where does 'smallest M' fail?
            byM=min(info, key=lambda z:(z[1], z[2]))
            if byM[4]!=setter:
                w=[z for z in info if z[4]==setter][0]
                fail_dM[w[1]-byM[1]]+=1
                fail_delta.append(float(w[2]-8*w[1]))
            w=[z for z in info if z[4]==setter][0]
            t=tnew; e=int(setter)//g; N=w[1]
            n+=1
print(f"  moves: {tot}")
print(f"  derived rule gives the same SCALE : {scale_eq}/{tot}   ({scale_eq/tot:.6f})")
print(f"  cases where it names a different blocker (a tie): {ident_miss}")
print(f"\n  where 'smallest M wins' fails: lap gap M_winner - M_smallest: {dict(sorted(fail_dM.items()))}")
if fail_delta:
    fail_delta.sort()
    print(f"  winner's delta = s - 8M in those cases: min {fail_delta[0]:.4f}  median {fail_delta[len(fail_delta)//2]:.4f}  max {fail_delta[-1]:.4f}")
    print(f"  (negative delta = the winner sits BELOW its multiple, as the analysis predicts)")
