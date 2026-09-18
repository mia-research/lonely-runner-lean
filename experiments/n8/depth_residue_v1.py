"""Owner: the neighbour result "bears on what runners are among the discrepancies and limits how
they may be arranged for any arrangement... more understanding about how and why any depth occurs".

Three tests, all on the decomposition  w = pi + 8 q.

(A) WHO CAN BIND.  At instant p the neighbour is at residue offset +-p, and p ranges over the
    UNITS {1,3,5,7}.  So only ODD offsets can ever be the tight pair at a grid instant; runners at
    EVEN offset always carry slack.  Test it, and measure how much slack.

(B) IS DEPTH A FUNCTION OF pi ALONE?  Matched pairs: same residues, different whole laps.
    If depth is residue-determined, q is invisible to depth too and depth is a finite object.

(C) IS THE BLOCKER SET residue-determined?  Same design, comparing WHO blocks, not how many.
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
def frac(x): return x-floor(x)
def gcd_all(u):
    g=0
    for a,b in combinations(u,2): g=gcd(g,abs(b-a))
    return g
def nextOp(d,t):
    k=floor(d*t-TH)
    while F(k)+TH<d*t: k+=1
    if k<0: k=0
    return (F(k)+TH)/d
def cascade_full(v,i):
    """Run the cascade on subject i, returning (t, depth, frozenset of runners that ever blocked)."""
    t=TH/min(abs(v[j]-v[i]) for j in range(8) if j!=i); n=0; blockers=set()
    while n<4000:
        b=[j for j in range(8) if j!=i and circd(F(abs(v[j]-v[i]))*t)<TH]
        if not b: return t,n,frozenset(blockers)
        blockers|=set(b)
        t=max(nextOp(F(abs(v[j]-v[i])),t) for j in b); n+=1
    return None,None,None
def build(rng,pi):
    q=[rng.randrange(0,7) for _ in range(8)]
    u=[pi[k]+8*q[k] for k in range(8)]
    if len(set(u))!=8 or gcd_all(u)!=1: return None
    order=sorted(range(8), key=lambda k: u[k])
    return speeds([u[k]-min(u)+1 for k in range(8)]), order

print("=== (A) at a grid instant, can an EVEN residue offset ever be the tight pair? ===")
rng=random.Random(31); odd=even=0; slack=Counter(); tested=0
while tested<400:
    pi=rng.sample(range(8),8)                       # a GRID: pi a bijection
    B=build(rng,pi)
    if B is None: continue
    tested+=1
    v,o=B
    for pos_i in range(8):
        tag=o[pos_i]
        for p in (1,3,5,7):
            t=F(p,8)
            sep=sorted((frac(F(v[j]-v[pos_i])*t), j) for j in range(8) if j!=pos_i)
            for rank,(s,j) in enumerate(sep):
                off=(pi[o[j]]-pi[tag])%8
                if rank==0 or rank==6:              # nearest ahead / nearest behind
                    if off%2==1: odd+=1
                    else: even+=1
                slack[off]=min(slack.get(off,F(9)), min(s,1-s))
print(f"   tight pair has ODD offset : {odd}     EVEN offset : {even}    ({tested} grids)")
print( "   closest any offset EVER comes to the subject, over all grids and instants:")
for off in range(1,8):
    print(f"      offset {off}: {float(slack[off]):.5f}   ({'threshold' if slack[off]==TH else 'slack'})")

print()
print("=== (B),(C) matched pairs: same residues pi, different whole laps q ===")
rng=random.Random(777)
dsame=btot=bsame=dtot=0; ddiff=Counter()
trials=0
while trials<2000:
    pi=[rng.randrange(8) for _ in range(8)]
    A=build(rng,pi); B=build(rng,pi)
    if A is None or B is None: continue
    trials+=1
    (v,oA),(w,oB)=A,B
    pA={oA[p]:p for p in range(8)}; pB={oB[p]:p for p in range(8)}
    for tag in range(8):
        tA,nA,blA=cascade_full(v,pA[tag]); tB,nB,blB=cascade_full(w,pB[tag])
        if nA is None or nB is None: continue
        dtot+=1
        if nA==nB: dsame+=1
        ddiff[nA-nB]+=1
        # blocker sets compared as MULTISETS OF RESIDUE OFFSETS, not indices
        sA=sorted((pi[oA[j]]-pi[tag])%8 for j in blA)
        sB=sorted((pi[oB[j]]-pi[tag])%8 for j in blB)
        btot+=1
        if sA==sB: bsame+=1
print(f"   depth identical            : {dsame} of {dtot}   ({dsame/dtot:.4f})")
print(f"   blocker offset-set identical: {bsame} of {btot}   ({bsame/btot:.4f})")
print(f"   depth difference distribution: {dict(sorted(ddiff.items())[:9])}")
