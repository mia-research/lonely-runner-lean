"""Hill-climb on the reading profile to maximise R, to test whether this implementation
reproduces the manuscript's max R = 11.965675 (band 1).  If it does, the cascade code here
matches theirs and downstream reasoning is on solid ground."""
from fractions import Fraction as F
import random
N=F(8)
def runR(S,cap=8000):
    R=F(1); seen=set()
    for _ in range(cap):
        key=tuple((s*R)%N for s in S)
        if key in seen: return None          # cycle -> non-terminating
        seen.add(key)
        out=[]
        for s in S:
            r=(s*R)%N
            if r<1: out.append((F(1)-r)/s)
            elif r>N-1: out.append((F(9)-r)/s)
        if not out: return R
        R=R+max(out)
    return None
random.seed(9)
Q=2000
best=(F(0),None)
for restart in range(60):
    xs=sorted(random.sample(range(Q+1,int(7.6*Q)),6))
    S=[F(1)]+[F(x,Q) for x in xs]
    cur=runR(S) or F(0)
    for it in range(4000):
        i=random.randrange(1,7)
        d=random.choice([-3,-2,-1,1,2,3])
        T=list(S); T[i]=T[i]+F(d,Q)
        if T[i]<=1: continue
        T=[T[0]]+sorted(T[1:])
        if len(set(T))!=7: continue
        v=runR(T)
        if v is not None and v>cur:
            S,cur=T,v
    if cur>best[0]: best=(cur,S)
R,S=best
print(f"  best R found = {float(R):.6f}")
print(f"  profile S    = {[round(float(x),4) for x in S]}")
print(f"  s_max        = {float(S[-1]):.4f}")
if R>0:
    prods=[(round(float(s),4), round(float(s*R),4)) for s in S]
    print(f"  readings s_i * R at the halt: {prods}")
print()
print("  manuscript §11.2: max R = 11.965675, binding constraint s7*R = 89, s7 ~ 7.437")
