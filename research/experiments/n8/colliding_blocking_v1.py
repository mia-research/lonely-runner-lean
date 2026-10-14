"""Cross-check a parallel session's colliding-pair analysis.

Their ALGEBRA is correct.  d = 8bg for a colliding pair, and
   |d/e - 8M/(8k+1)| < 1/(8k+1)   ==>   |bg/e - M/(8k+1)| < 1/(8(8k+1))     (Case 1)
   |d/(8bg) - 8M/(8k+1)| < 1/(8k+1) ==> |u_d - 64bM/(8k+1)| < 8b/(8k+1)     (Case 2)
Both derivations verified by hand and reproduced below symbolically.

Their INFERENCES are what this tests.  Both are obtained by dividing (or multiplying) BOTH SIDES
of one inequality -- which cannot change which (M,k) satisfy it.  Case 1's "8x tighter tolerance,
rarely blocks" and Case 2's "fast exit" would have to show up as a measurable difference between
colliding and non-colliding disparities.  Measured here.

This is the same move already recorded in experiments/n8/Bridge_v1.lean, whose docstring notes that
multiplying through by (8k+1) leaves "|numerator - 8M| < 1", i.e. a congruence, with the
approximation quality 1/q free -- no Diophantine content.

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
    m=min(ds); t=TH/m; n=0; blocks=Counter()
    while n<4000:
        b=[d for d in ds if circd(d*t)<TH]
        if not b: return t,n,blocks
        for d in b: blocks[d]+=1
        t=max(nextOp(d,t) for d in b); n+=1
    return None,None,None

print("=== algebra check (both cases, symbolic on random instances) ===")
rng=random.Random(4); ok1=ok2=0
for _ in range(2000):
    b=rng.randrange(1,9); g=rng.randrange(1,9); e=F(rng.randrange(1,200))
    M=rng.randrange(0,9); k=rng.randrange(0,9)
    d=8*b*g
    L=abs(F(d)/e - F(8*M,8*k+1)) < F(1,8*k+1)
    R=abs(F(b*g)/e - F(M,8*k+1)) < F(1,8*(8*k+1))
    ok1 += (L==R)
    e2=F(8*b*g); dd=rng.randrange(1,400)
    L2=abs(F(dd)/e2 - F(8*M,8*k+1)) < F(1,8*k+1)
    R2=abs(F(dd,g) - F(64*b*M,8*k+1)) < F(8*b,8*k+1)
    ok2 += (L2==R2)
print(f"  Case 1 restatement equivalent to the original: {ok1}/2000")
print(f"  Case 2 restatement equivalent to the original: {ok2}/2000")
print("  => both are EXACT restatements. The same (M,k) satisfy them. No condition was tightened.")

print("\n=== does a colliding disparity block LESS often?  (Case 1's 'sparse blocking') ===")
rng=random.Random(99)
col_block=col_tot=non_block=non_tot=0
depths_col=[]; depths_non=[]
for _ in range(1500):
    v=speeds(rng.sample(range(1,90),8))
    g=gcd_all(v)
    for i in range(8):
        ds=[F(abs(v[j]-v[i])) for j in range(8) if j!=i]
        t,n,blocks=cascade(ds)
        if t is None: continue
        subj_colliding = any((int(d)//g)%8==0 for d in ds)
        (depths_col if subj_colliding else depths_non).append(n)
        for d in ds:
            colliding = (int(d)//g)%8==0
            if colliding: col_tot+=1; col_block += 1 if blocks.get(d,0)>0 else 0
            else:         non_tot+=1; non_block += 1 if blocks.get(d,0)>0 else 0
print(f"  colliding disparities that ever block : {col_block}/{col_tot}  ({col_block/col_tot:.4f})")
print(f"  non-colliding that ever block         : {non_block}/{non_tot}  ({non_block/non_tot:.4f})")

print("\n=== their 'mean 2.41 moves' for colliding subjects ===")
print(f"  subjects WITH a colliding disparity : n={len(depths_col)}  mean depth {sum(depths_col)/len(depths_col):.3f}  max {max(depths_col)}")
print(f"  subjects WITHOUT                    : n={len(depths_non)}  mean depth {sum(depths_non)/len(depths_non):.3f}  max {max(depths_non)}")
