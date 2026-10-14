"""Sample where the manuscript's deep cases live: spread S = s_max just above 7,
i.e. where the ratio condition d_max <= 7 d_min JUST fails."""
from fractions import Fraction as F
import random
N=F(8)
def blk(S,R):
    out=[]
    for s in S:
        r=(s*R)%N
        if r<1: out.append((s,(F(1)-r)/s))
        elif r>N-1: out.append((s,(F(9)-r)/s))
    return out
def run(S,cap=20000):
    R=F(1); seen={}; k=0
    for j in range(cap):
        key=tuple((s*R)%N for s in S)
        if key in seen: return "CYCLE",j,R
        seen[key]=j
        b=blk(S,R)
        if not b: return "CLEAR",j,R
        R=R+max(x for _,x in b); k=j
    return "CAP",cap,R
random.seed(101)
print("  spread band      profiles  max R seen   R>9   R>7   mean moves   cycles")
for lo,hi,Q in [(7,8,120),(8,10,120),(10,20,120),(20,60,120),(2,400,1)]:
    best=F(0); n9=n7=0; tot=0; mv=0; cyc=0
    for _ in range(6000):
        if Q==1:
            D=[1]+sorted(random.sample(range(2,400),6))
            S=[F(x) for x in D]
        else:
            # readings 1 = s1 < ... < s7 with s7 in (lo,hi), denominators Q
            xs=sorted(random.sample(range(Q+1, int(hi*Q)), 6))
            S=[F(1)]+[F(x,Q) for x in xs]
            if not (lo < S[-1] < hi): continue
        st,j,R=run(S); tot+=1; mv+=j
        if st=="CYCLE": cyc+=1
        if R>best: best=R
        if R>9: n9+=1
        if R>7: n7+=1
    print(f"  s_max in ({lo},{hi})  {tot:8d}  {float(best):10.4f} {n9:5d} {n7:6d} {mv/max(tot,1):11.2f} {cyc:8d}")
