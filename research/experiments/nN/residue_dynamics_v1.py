"""The cascade as a map on the RESIDUE VECTOR r_i = s_i*R mod 8.
(1) the step is a function of r alone;  (2) for integer readings r lives in a finite set,
so the orbit is eventually periodic;  (3) in a cycle the residues return, forcing
s_i * Delta = 0 mod 8 for every i -- and s_1 = 1 then forces Delta in 8Z."""
from fractions import Fraction as F
import random
N=8
def blockers(S,R):
    out=[]
    for s in S:
        r=(s*R)%N
        if r<1: out.append((s,(F(1)-r)/s))
        elif r>N-1: out.append((s,(F(N+1)-r)/s))
    return out
def step_from_residues(S,R):
    b=blockers(S,R)
    return (max(x for _,x in b) if b else None)
def run(S,cap=5000):
    R=F(1); seen={}; orb=[]
    for j in range(cap):
        key=tuple((s*R)%N for s in S)
        if key in seen: return orb,("CYCLE",seen[key],j,R)
        seen[key]=j; orb.append(R)
        st=step_from_residues(S,R)
        if st is None: return orb,("CLEAR",j,R)
        R=R+st
    return orb,("CAP",)
print("=== 1. step is a function of the residue vector alone ===")
random.seed(5); bad=tot=0
for _ in range(300):
    S=[F(1)]+[F(x) for x in sorted(random.sample(range(2,50),6))]
    R=F(1)
    for _ in range(40):
        st=step_from_residues(S,R)
        if st is None: break
        # recompute via the direct move law and compare
        blk=[]
        for s in S:
            x=s*R; M=round(x/N)
            if M>=0 and abs(x-N*M)<1: blk.append(F(N*M+1,1)/s-R)
        tot+=1
        if not blk or max(blk)!=st: bad+=1
        R=R+st
print(f"    checked {tot} steps against the direct move law: mismatches = {bad}")
print()
print("=== 2. does any profile enter a CYCLE (non-termination) ? ===")
random.seed(17); res={"CLEAR":0,"CYCLE":0,"CAP":0}; cyc=[]
for _ in range(4000):
    S=[F(1)]+[F(x) for x in sorted(random.sample(range(2,120),6))]
    orb,r=run(S)
    res[r[0]]+=1
    if r[0]=="CYCLE": cyc.append(([int(x) for x in S],r))
print(f"    {res}")
if cyc: print("    cycle examples:",cyc[:3])
print()
print("=== 3. the cycle rigidity, derived:  r_i returns  =>  s_i*Delta = 0 mod 8 for all i ===")
print("    with s_1 = 1 that forces Delta in 8Z, so Delta >= 8: a cycle crosses a whole band.")
print("    steps are < 2/s <= 2, so a cycle needs at least 5 moves.")
