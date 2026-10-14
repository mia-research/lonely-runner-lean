"""Two claims to break, not to admire.
 C1: when d_min blocks with r_1 in (7,8), its step 9-r_1 is in (1,2), while any other blocker
     with reading s has step < 2/s <= 1 for s >= 2.  So d_min WINS and R lands exactly on 8k+9.
 C2: at an integer R = 1 mod 8 the residues are r_i = s_i mod 8 -- the SAME as at R_0 = 1.
     So revisiting such a point repeats the whole orbit: a cycle, hence non-termination.
Tested with INTEGER readings and then with RATIONAL ones (d_min need not divide the rest)."""
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
def run(S,cap=3000):
    R=F(1); seen={}
    for j in range(cap):
        key=tuple((s*R)%N for s in S)
        if key in seen: return "CYCLE",j,R,seen[key]
        seen[key]=j
        b=blk(S,R)
        if not b: return "CLEAR",j,R,None
        R=R+max(x for _,x in b)
    return "CAP",cap,R,None
def probe(S):
    """does d_min ever lose while r_1 in (7,8)?  does R ever hit an integer = 1 mod 8 after start?"""
    R=F(1); lose=hit=0
    for _ in range(3000):
        b=blk(S,R)
        if not b: break
        best=max(x for _,x in b)
        r1=R%N
        if r1>N-1:
            dm=[x for s,x in b if s==1]
            if dm and dm[0]<best: lose+=1
        R=R+best
        if R.denominator==1 and R%N==1: hit+=1
    return lose,hit
random.seed(2024)
for label,gen in [("INTEGER readings", lambda: [F(1)]+[F(x) for x in sorted(random.sample(range(2,90),6))]),
                  ("RATIONAL readings", lambda: (lambda D: [F(d,D[0]) for d in D])(sorted(random.sample(range(3,200),7))))]:
    L=H=0; res={"CLEAR":0,"CYCLE":0,"CAP":0}; band1=0
    for _ in range(4000):
        S=gen()
        if S[0]!=1: continue
        st,j,R,_=run(S); res[st]+=1
        if R>9: band1+=1
        l,h=probe(S); L+=l; H+=h
    print(f"  {label:20s} {res}   orbits reaching R>9: {band1}")
    print(f"      d_min blocked in (7,8) but LOST the max : {L}")
    print(f"      landings on an integer R = 1 mod 8 after the start : {H}")
