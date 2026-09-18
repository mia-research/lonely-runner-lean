"""v1/v2: the residues pi do NOT predict cascade depth (0.4018 vs a forced floor of 0.3752).
That is a negative for pi.  The complement is the obvious next test and was not run.

GridNeighbour_v1.lean proves q is invisible at the grid instants -- pi governs those completely.
If depth is the q-phenomenon, then matching q (and varying pi) should pin depth the way matching
pi pinned the grid neighbour.  Three arms, one statistic:

    matched pi (q varies) | matched q (pi varies) | matched neither
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
def cascade_depth(v,i):
    t=TH/min(abs(v[j]-v[i]) for j in range(8) if j!=i); n=0
    while n<4000:
        b=[j for j in range(8) if j!=i and circd(F(abs(v[j]-v[i]))*t)<TH]
        if not b: return n
        t=max(nextOp(F(abs(v[j]-v[i])),t) for j in b); n+=1
    return None
def build(pi,q):
    u=[pi[k]+8*q[k] for k in range(8)]
    if len(set(u))!=8 or gcd_all(u)!=1: return None
    return speeds([u[k]-min(u)+1 for k in range(8)]), sorted(range(8), key=lambda k: u[k])
def run(rng,arm,N=2500):
    same=tot=0; dep=Counter()
    trials=0
    while trials<N:
        piA=[rng.randrange(8) for _ in range(8)]; qA=[rng.randrange(0,7) for _ in range(8)]
        piB=piA if arm=='pi' else [rng.randrange(8) for _ in range(8)]
        qB =qA  if arm=='q'  else [rng.randrange(0,7) for _ in range(8)]
        A=build(piA,qA); B=build(piB,qB)
        if A is None or B is None: continue
        trials+=1
        (v,oA),(w,oB)=A,B
        pA={oA[p]:p for p in range(8)}; pB={oB[p]:p for p in range(8)}
        for tag in range(8):
            nA=cascade_depth(v,pA[tag]); nB=cascade_depth(w,pB[tag])
            if nA is None or nB is None: continue
            tot+=1; dep[nA]+=1
            if nA==nB: same+=1
    return same/tot, tot, dep
r={}
for arm,seed in (('pi',777),('q',3131),('none',5150)):
    r[arm]=run(random.Random(seed),arm)
s=sum(r['none'][2].values())
floor_=sum((c/s)**2 for c in r['none'][2].values())
print("  depth agreement between two arrangements, by what is held fixed:")
print(f"     matched pi  (q varies)   {r['pi'][0]:.4f}")
print(f"     matched q   (pi varies)  {r['q'][0]:.4f}")
print(f"     matched neither          {r['none'][0]:.4f}")
print(f"     forced floor             {floor_:.4f}    (collision rate of the depth marginal)")
print(f"  n ~ {r['pi'][1]} subject-pairs per arm")
