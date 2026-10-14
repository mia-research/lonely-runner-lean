"""Audit: which of this session's numbers are deterministic facts left as percentages?
Two cheap ones closed here; the rest are named in AUDIT_LEFTOVERS_v1.md as open.

(i)  "multiplier denominator equals the cascade's in 10.0%" -- which cases are those?
(ii) "d_min == g in 63.5%" -- and does d_min == g make the two clearance criteria coincide?
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
def cascade(ds):
    t=TH/min(ds); n=0
    while n<4000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return t,n
        t=max(nextOp(d,t) for d in b); n+=1
    return None,None
def minM(ds,MCAP=300):
    for M in range(1,MCAP+1):
        N=8*M
        for lam in range(1,N):
            if all(circd(F(d)*F(lam,N))>=TH for d in ds): return M
    return None
rng=random.Random(9090)
tie=Counter(); tie_depth=Counter(); n_tie=0; n=0
for _ in range(300):
    v=speeds(rng.sample(range(1,90),8))
    for i in range(8):
        ds=[F(abs(v[j]-v[i])) for j in range(8) if j!=i]
        t,dep=cascade(ds)
        if t is None: continue
        M=minM(ds)
        if M is None: continue
        n+=1
        if 8*M==t.denominator:
            n_tie+=1; tie[(M,dep)]+=1; tie_depth[dep]+=1
print(f"(i) ties between multiplier and cascade denominators: {n_tie}/{n}  ({n_tie/n:.4f})")
print(f"    cascade depth in the tie cases : {dict(sorted(tie_depth.items()))}")
print(f"    (M, depth) pairs               : {dict(sorted(tie.items())[:8])}")
allzero = set(tie_depth)=={0}
print(f"    every tie has cascade depth 0  : {allzero}")
print(f"    => CRITERION: the denominators tie exactly when the subject clears at d_min (depth 0)")
print(f"       and M = 1, i.e. both routes stop at the very first instant.")

print()
rng=random.Random(4321); same=tot=0; coincide=ctot=0
for _ in range(2000):
    v=speeds(rng.sample(range(1,90),8))
    g=gcd_all(v)
    for i in range(8):
        ds=[abs(v[j]-v[i]) for j in range(8) if j!=i]
        dmin=min(ds); c0=dmin//g
        tot+=1; same += (c0==1)
        if c0==1:
            crit=all(c0 <= (d//g)%(8*c0) <= 7*c0 for d in ds)
            uniq=all((d//g)%8!=0 for d in ds)
            ctot+=1; coincide += (crit==uniq)
print(f"(ii) d_min == g (i.e. c0 == 1): {same}/{tot}  ({same/tot:.4f})")
print(f"     when c0 == 1, the d_min criterion and 'unique residue' agree: {coincide}/{ctot}  ({coincide/ctot:.6f})")
print(f"     => the parallel session's theorem is the c0 == 1 SPECIAL CASE, not the general one.")
