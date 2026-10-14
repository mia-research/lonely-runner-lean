"""The move in the R coordinate.
Algebra:  reading of d_i at scale D is s_i*R.  A blocker at lap M has |s_i R - 8M| < 1;
its next opening is the scale D' = d_i/(8M+1), i.e.  R' = d_min/D' = (8M+1)/s_i.
The move takes the LARGEST next opening, hence   R_{j+1} = max over blockers (8M_i+1)/s_i.
So the orbit lands EXACTLY on the candidate family {(8m+1)/s}, and the step is closed form."""
from fractions import Fraction as F
from math import floor
N=8
def cd(x):
    f=x-int(x)
    if f<0: f+=1
    return min(f,1-f)
def cascade_R(S,cap=4000):
    """S = reading profile with S[0]=1.  Returns the R-orbit."""
    R=F(1); orbit=[R]
    for _ in range(cap):
        blk=[]
        for s in S:
            x=s*R
            M=round(x/N)
            if abs(x-N*M)<1 and M>=0: blk.append((s,M))
        if not blk: return orbit,True
        Rn=max(F(N*M+1,1)/s for s,M in blk)
        if Rn<=R: return orbit,False
        R=Rn; orbit.append(R)
    return orbit,None
print("=== R_{j+1} = max over blockers of (8M+1)/s  — checked against the direct cascade ===")
import random
random.seed(8)
bad=0; tot=0; steps=[]
for _ in range(400):
    S=[1]+sorted(random.sample(range(2,60),6))
    orb,term=cascade_R(S)
    if term is None: continue
    tot+=1
    # every visited R must be of the form (8m+1)/s for some s in S
    for R in orb[1:]:
        ok=any((R*s).denominator==1 and (int(R*s)-1)%N==0 for s in S)
        if not ok: bad+=1
    for a,b in zip(orb,orb[1:]): steps.append(float(b-a))
print(f"    profiles {tot};  visited R not of the form (8m+1)/s : {bad}")
print(f"    steps recorded: {len(steps)};  max step {max(steps):.4f};  mean {sum(steps)/len(steps):.4f}")
print()
print("=== is every step < 1 ?  (d_min never blocks, so the blocker has s > 1) ===")
print(f"    steps >= 1 : {sum(1 for x in steps if x>=1)}")
print(f"    step size vs 1/s of the winner — the advance is 1/s_winner up to the lap offset")
