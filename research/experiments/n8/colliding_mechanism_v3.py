"""Last unexplained fact: near colliding blocks split 731 'just below a multiple of 8' vs 260
'just above'.  The bad zone (8M-1, 8M+1) has equal halves, so a uniform null gives 50:50.

HYPOTHESIS.  Readings s = d/D grow monotonically along the cascade (D strictly decreases).  The
move sets t' = max over blockers of their next opening, so EVERY blocker is at or past its opening
and has exited its current bad zone.  A blocker that is bad again has overshot into the NEXT zone,
which is entered from BELOW -- s just under 8(M+1).  That is exactly the r > 7c/8 side.

So the asymmetry should be (a) accompanied by the blocker's lap index INCREASING, and (b) stronger
when the dilation is small (small jumps land just inside the next zone).  Both testable.
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
rng=random.Random(1234)
mono_ok=mono_tot=0
side_by_lapmove=Counter(); dil_by_side={'below8M':[], 'above8M':[]}
for _ in range(2500):
    v=speeds(rng.sample(range(1,90),8))
    g=gcd_all(v)
    for i in range(8):
        ds=sorted(F(abs(v[j]-v[i])) for j in range(8) if j!=i)
        col={d for d in ds if (int(d)//g)%8==0}
        if not col: continue
        t=TH/min(ds); n=0; prevlap={}; prevt=None
        while n<4000:
            b=[d for d in ds if circd(d*t)<TH]
            if not b: break
            if prevt is not None:
                mono_tot+=1; mono_ok += (t>prevt)
            for d in b:
                if d not in col: continue
                s=d/(1/(8*t))
                if s.denominator==1 and int(s)%8==0: continue     # exact, not a near block
                M=round(s/8); side = 'below8M' if s<8*M else 'above8M'
                lap=int(s//8)
                moved = 'lap moved' if prevlap.get(d) is not None and lap>prevlap[d] else \
                        ('lap same' if prevlap.get(d) is not None else 'first sight')
                side_by_lapmove[(side,moved)]+=1
                if prevt is not None: dil_by_side[side].append(float(t/prevt))
            for d in b: prevlap[d]=int((d/(1/(8*t)))//8)
            prevt=t
            t=max(nextOp(d,t) for d in b); n+=1
print(f"  readings grow monotonically (t strictly increases): {mono_ok}/{mono_tot}  ({mono_ok/mono_tot:.6f})\n")
print("  near colliding blocks, by side and by whether the blocker's lap index advanced:")
tot=sum(side_by_lapmove.values())
for k in sorted(side_by_lapmove, key=lambda x:(-side_by_lapmove[x])):
    print(f"    {k[0]:<9} {k[1]:<12} {side_by_lapmove[k]:>5}   ({side_by_lapmove[k]/tot:.4f})")
for s in ('below8M','above8M'):
    a=dil_by_side[s]
    if a: print(f"\n  mean dilation t/t_prev when side = {s:<9}: {sum(a)/len(a):.5f}   n={len(a)}")
