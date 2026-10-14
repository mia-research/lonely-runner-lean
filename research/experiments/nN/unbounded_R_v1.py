"""Is R bounded across arrangements?  Sample where the residue line has a LONG period:
readings p_i/q with large q (approximating irrational ratios), spread just above 7."""
from fractions import Fraction as F
import random
N=F(8)
def run(S,cap=2000000):
    R=F(1)
    for _ in range(cap):
        out=[]
        for s in S:
            r=(s*R)%N
            if r<1: out.append((F(1)-r)/s)
            elif r>N-1: out.append((F(9)-r)/s)
        if not out: return R
        R=R+max(out)
    return None
random.seed(20260922)
print("  denominator q   profiles   max R found   (12.714 = the manuscript's stated ceiling)")
overall=F(0); wit=None
for q in (30,120,500,2000,10000,60000):
    best=F(0); tot=0; bw=None
    trials = 12000 if q<=2000 else 4000
    for _ in range(trials):
        xs=sorted(random.sample(range(q+1,int(7.5*q)),6))
        S=[F(1)]+[F(x,q) for x in xs]
        if len(set(S))!=7: continue
        tot+=1
        R=run(S)
        if R is None: continue
        if R>best: best,bw=R,S
    if best>overall: overall,wit=best,bw
    flag="  <-- exceeds 12.714" if float(best)>12.714 else ""
    print(f"  q = {q:6d} {tot:11d}   {float(best):11.5f}{flag}")
print()
print(f"  largest R over the whole run: {float(overall):.6f}")
if wit: print(f"    profile: {[round(float(s),6) for s in wit]}  spread {float(wit[-1]):.5f}")
