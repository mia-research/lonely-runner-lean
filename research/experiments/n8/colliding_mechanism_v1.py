"""The signal survives the size control (1.93x pooled), so it is a residue effect.  Mechanism?

Cascade scales are D = d'/(8N+1) with d' = c.g a disparity.  For a blocker d = a.g the reading is
    s = d/D = a(8N+1)/c
Blocking is  |s - 8M| < 1  for some integer M.  Split by whether a is a multiple of 8:

    COLLIDING     a = 8b :  |8b(8N+1)/c - 8M| < 1   <=>  |b(8N+1)/c - M| < 1/8
                            -- near ANY INTEGER, denominator c
    NON-COLLIDING a != 0 mod 8 : |a(8N+1)/c - 8M| < 1
                            -- near a MULTIPLE OF 8, denominator 8c

Equal MEASURE (1/4 each).  But EXACT hits differ by a factor of 8:
    colliding exact     needs  c | b(8N+1)          density ~ 1/c
    non-colliding exact needs  8c | a(8N+1)         density ~ 1/(8c)

PREDICTION: colliding blocks are far more often EXACT (reading an exact multiple of 8), and that
is what drives the 1.93x.  Test it.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
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
cx=ct=nx=nt=0            # exact / total blocking events, colliding vs not
for _ in range(2500):
    v=speeds(rng.sample(range(1,90),8))
    g=gcd_all(v)
    for i in range(8):
        ds=sorted(F(abs(v[j]-v[i])) for j in range(8) if j!=i)
        col={d for d in ds if (int(d)//g)%8==0}
        if not col: continue
        t=TH/min(ds); n=0
        while n<4000:
            b=[d for d in ds if circd(d*t)<TH]
            if not b: break
            for d in b:
                s=d/(1/(8*t))            # reading  s = d / D,  D = 1/(8t)
                exact = (s.denominator==1 and int(s)%8==0)
                if d in col: ct+=1; cx+=exact
                else:        nt+=1; nx+=exact
            t=max(nextOp(d,t) for d in b); n+=1
print(f"  blocking events, colliding     : {ct:>7}   of which EXACT (reading a multiple of 8): {cx:>7}  ({cx/ct:.4f})")
print(f"  blocking events, non-colliding : {nt:>7}   of which EXACT                          : {nx:>7}  ({nx/nt:.4f})")
if nx: print(f"\n  ratio of exact-hit rates: {(cx/ct)/(nx/nt):.2f}x   (algebra predicts ~8x)")
else:  print(f"\n  non-colliding NEVER blocks exactly -- the predicted 8x is a floor, not a ratio.")
