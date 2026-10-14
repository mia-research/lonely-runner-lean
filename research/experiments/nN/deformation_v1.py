"""The deformation picture: R measures how far the arrangement is pushed from the AP.
AP  => readings 1..7, d_max = 7 d_min, R = 1 (Theorem 8).
Test: (a) how does max R behave as the spread S grows?  (b) is the BINDING LAP INDEX bounded?
Sampled with RATIONAL readings (integer disparities, d_min need NOT divide them)."""
from fractions import Fraction as F
import random
N=F(8)
def run(S,cap=200000):
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
def binding_M(S,R):
    """at the halt, the lap index of each reading: M_i = floor(s_i R / 8); report the max"""
    return max(int((s*R)//N) for s in S)
random.seed(4242)
print("  AP check: readings 1..7 ->", run([F(i) for i in range(1,8)]))
print()
print("  spread S      profiles   max R      max binding lap M   (89/S for reference)")
for lo,hi in [(7.0,7.2),(7.2,7.6),(7.6,8.5),(8.5,11),(11,20),(20,60),(60,200)]:
    best=F(0); bestM=0; tot=0
    for _ in range(40000):
        dmin=random.randrange(20,120)
        ds=[dmin]+sorted(random.sample(range(dmin+1,int(hi*dmin)+1),6))
        S=[F(d,dmin) for d in ds]
        s=float(S[-1])
        if not (lo<s<hi): continue
        tot+=1
        R=run(S)
        if R is None: continue
        if R>best: best=R
        M=binding_M(S,R)
        if M>bestM: bestM=M
    ref=89/((lo+hi)/2)
    print(f"  ({lo:5.1f},{hi:5.1f}) {tot:9d}  {float(best):9.4f} {bestM:16d}      {ref:8.2f}")
