"""The cage read as a perturbation budget.

At instant t = p/8 a runner at residue offset D sits at slot (D*p mod 8)/8.  Moving its speed by
delta (reduced units) moves it by delta*t = delta*p/8.  The subject stays clear while the runner
stays at circle-distance >= 1/8.  So the budget is

    delta_max  =  (dist(D,p) - 1/8) / t  =  (dist(D,p) - 1/8) * 8/p

Exhaustive over offsets and instants -- no sampling -- then checked against a direct simulation
on real grids.  All speeds positive."""
import sys; sys.path.insert(0,'experiments/n8')
from _frame import speeds
from fractions import Fraction as F
from math import floor, gcd
from itertools import combinations
import random
TH=F(1,8)
def circd(x):
    x=x-floor(x); return min(x,1-x)
def nu2(d):
    k=0
    while d%2==0: d//=2; k+=1
    return k
print("  exact budget: how far a runner's speed may move before the subject stops being clear")
print("  offset  nu2   budget at p=1   p=3    p=5    p=7     MIN over the four instants")
for D in range(1,8):
    b=[]
    for p in (1,3,5,7):
        dist=circd(F(D*p,8))
        b.append((dist-TH)*8/p)
    print(f"    {D}     {nu2(D)}     " + "  ".join(f"{str(x):>6}" for x in b) + f"      {min(b)}")
print()
print("  direct simulation on real grids: largest integer shift of one runner's speed that keeps")
print("  the subject clear at t = 1/8, by that runner's residue offset")
rng=random.Random(88); best={}
tested=0
while tested<300:
    pi=rng.sample(range(8),8)
    q=[rng.randrange(0,7) for _ in range(8)]
    u=[pi[k]+8*q[k] for k in range(8)]
    if len(set(u))!=8: continue
    g=0
    for a,b2 in combinations(u,2): g=gcd(g,abs(b2-a))
    if g!=1: continue
    tested+=1
    v=speeds([x-min(u)+1 for x in u]); o=sorted(range(8), key=lambda k: u[k])
    for pos_i in range(8):
        tag=o[pos_i]
        for pos_j in range(8):
            if pos_j==pos_i: continue
            D=(pi[o[pos_j]]-pi[tag])%8
            # largest |shift| keeping THIS runner clear of the subject at t = 1/8
            s=0
            while s<12 and circd(F(v[pos_j]+s+1-v[pos_i],1)*F(1,8))>=TH \
                       and circd(F(v[pos_j]-s-1-v[pos_i],1)*F(1,8))>=TH: s+=1
            best[D]=min(best.get(D,99),s)
print("    offset : min observed integer budget")
for D in sorted(best): print(f"      {D}    : {best[D]}")
