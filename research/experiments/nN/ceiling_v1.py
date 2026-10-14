"""Directed climb from the known deep case, testing the stated ceiling R <= 89/7 = 12.714.
The ceiling rests on the binding numerator being 89 = 8*11+1.  If a profile binds at a LARGER
numerator, the ceiling is not a bound."""
from fractions import Fraction as F
import random
N=F(8)
def run(S,cap=500000):
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
def binding(S,R):
    """the numerator 8M+1 of the binding constraint at the halt: the reading sitting on a lower edge"""
    best=None
    for s in S:
        v=s*R
        M=int(v//N)
        if v-N*M>=1 and (best is None or N*M+1>best): best=N*M+1
    return best
BASE=[30,74,96,127,159,175,224]
S0=[F(d,30) for d in BASE]
print(f"  start: BASE  R = {float(run(S0)):.6f}  binding numerator = {binding(S0,run(S0))}")
random.seed(7)
best=(run(S0),S0)
for restart in range(40):
    S=list(best[1]); cur=best[0]
    q=random.choice([240,600,1500,4000])
    S=[F(1)]+[F(round(float(s)*q),q) for s in S[1:]]
    S=[S[0]]+sorted(set(S[1:]))
    if len(S)!=7: continue
    cur=run(S) or F(0)
    for it in range(3000):
        i=random.randrange(1,7)
        T=list(S); T[i]=T[i]+F(random.choice([-2,-1,1,2]),q)
        if T[i]<=1: continue
        T=[T[0]]+sorted(set(T[1:]))
        if len(T)!=7: continue
        v=run(T)
        if v is not None and v>cur: S,cur=T,v
    if cur>best[0]: best=(cur,S)
R,S=best
print(f"  best R found = {float(R):.6f}")
print(f"  binding numerator at the halt = {binding(S,R)}   (89 at the manuscript's maximiser)")
print(f"  profile spread S = {float(S[-1]):.5f}")
print(f"  exceeds the stated ceiling 12.714 ? {float(R)>12.714}")
