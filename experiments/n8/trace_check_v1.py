"""Verify the parallel session's 23-step trace, then answer the witness question ON THEIR EXAMPLE.

Their claims for subject v=1 of (1,31,75,97,128,160,176,225):
  disparities {30,74,96,127,159,175,224}; colliding (8|d): 96, 224
  23 moves; D_final = 32/11; t* = 11/256; R = 165/16; colliding set 7 of 23 steps
All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
v=speeds((1,31,75,97,128,160,176,225))
i=0
ds=sorted(F(abs(v[j]-v[i])) for j in range(8) if j!=i)
g=0
for a,b in combinations(v,2): g=gcd(g,abs(b-a))
print(f"  arrangement {list(v)}  subject {v[i]}  g = {g}")
print(f"  disparities {[int(d) for d in ds]}")
print(f"  colliding (8 | d/g): {[int(d) for d in ds if (int(d)//g)%8==0]}")
t=TH/min(ds); n=0; setters=[]
while n<4000:
    b=[d for d in ds if circd(d*t)<TH]
    if not b: break
    cands=[(nextOp(d,t),d) for d in b]
    t,setter=max(cands)
    setters.append(int(setter)); n+=1
Dfin=1/(8*t)
print(f"\n  moves                      : {n}          (they say 23)")
print(f"  D_final                    : {Dfin}     (they say 32/11)")
print(f"  t*                         : {t}      (they say 11/256)")
print(f"  R = d_min/D_final          : {min(ds)/Dfin}    (they say 165/16)")
col=[s for s in setters if (s//g)%8==0]
print(f"  setters                    : {setters}")
print(f"  colliding setters          : {len(col)} of {n}  ({len(col)/n:.3f})   (they say 7 of 23)")
print(f"  which                      : 224 sets {setters.count(224)}x, 96 sets {setters.count(96)}x")

print("\n=== the witness question, on THIS subject ===")
def minM(ds,MCAP=400):
    for M in range(1,MCAP+1):
        N=8*M
        for lam in range(1,N):
            tt=F(lam,N)
            if all(circd(F(d)*tt)>=TH for d in ds): return M,lam
    return None,None
M,lam=minM(ds)
print(f"  cascade    : t = {t}  denominator {t.denominator}, after {n} moves")
print(f"  multiplier : t = {F(lam,8*M)}   denominator {8*M}, found by scanning M = 1..{M}")
print(f"  check      : min distance = {min(circd(F(d)*F(lam,8*M)) for d in ds)}  (threshold 1/8)")
print(f"\n  denominator ratio: {t.denominator}/{8*M} = {t.denominator/(8*M):.2f}x simpler")
