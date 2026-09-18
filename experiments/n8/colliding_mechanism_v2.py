"""Owner: "the rest must occur for a reason. It's not like they change if we run them again."
Correct -- 81.3%/18.7% is a deterministic arithmetic partition, not a sample.  Characterise it.

A colliding blocker d = 8bg at cascade scale D = cg/(8N+1) reads  s = 8b(8N+1)/c.
Let r = b(8N+1) mod c.  Then blocking is  min(r/c, 1-r/c) < 1/8, and:

  r = 0                   ->  EXACT block       (c | b(8N+1))
  0 < r < c/8             ->  near block, from below
  7c/8 < r < c            ->  near block, from above

With r an integer >= 1, both near cases need c/8 > 1, i.e.

  PREDICTION: a NON-EXACT colliding block requires c > 8  (host disparity > 8 in reduced units).
  Equivalently: if c <= 8, EVERY colliding block is exact.

Tested exhaustively over the same population.  All speeds positive."""
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
rng=random.Random(1234)
exact=0; near=0
viol_pred=0; c_of_near=Counter(); c_of_exact=Counter()
r_side=Counter(); div_agrees=0; div_tot=0
for _ in range(2500):
    v=speeds(rng.sample(range(1,90),8))
    g=gcd_all(v)
    for i in range(8):
        ds=sorted(F(abs(v[j]-v[i])) for j in range(8) if j!=i)
        col={d for d in ds if (int(d)//g)%8==0}
        if not col: continue
        # track the scale as (c, N) so the algebra is available, not just the number
        c_cur=int(min(ds))//g; N_cur=0                     # D_0 = d_min = c.g/(8.0+1)
        t=TH/min(ds); n=0
        while n<4000:
            b=[d for d in ds if circd(d*t)<TH]
            if not b: break
            for d in b:
                if d not in col: continue
                bb=(int(d)//g)//8
                q=bb*(8*N_cur+1); r=q % c_cur
                s=d/(1/(8*t))
                is_exact = (s.denominator==1 and int(s)%8==0)
                div_tot+=1; div_agrees += ((r==0)==is_exact)   # check r=0 <-> exact
                if is_exact: exact+=1; c_of_exact[c_cur]+=1
                else:
                    near+=1; c_of_near[c_cur]+=1
                    if c_cur<=8: viol_pred+=1
                    r_side['below' if r*8<c_cur else 'above']+=1
            # advance, recording the new scale's (c, N)
            cands=[(nextOp(d,t),d) for d in b]
            t,setter=max(cands)
            c_cur=int(setter)//g; N_cur=int(setter*t-TH)
            n+=1
print(f"  colliding blocking events: exact {exact}   near {near}   ({exact/(exact+near):.4f} exact)\n")
print(f"  criterion  r = 0  <->  exact block : {div_agrees}/{div_tot} agree  ({div_agrees/div_tot:.6f})")
print(f"\n  PREDICTION: no near block with c <= 8.   violations: {viol_pred}")
print(f"  smallest c among NEAR blocks  : {min(c_of_near) if c_of_near else None}")
print(f"  largest  c among EXACT blocks : {max(c_of_exact) if c_of_exact else None}")
print(f"\n  c-distribution of NEAR blocks (smallest 10): {sorted(c_of_near.items())[:10]}")
print(f"  which side of the integer: {dict(r_side)}")
