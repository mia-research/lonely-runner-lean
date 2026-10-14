# (i) made precise: the three speeds are the SUBJECT (at 0) and its TWO NEIGHBOURS on the circle.
# At a flank opening the flank IS one neighbour, at exactly 1/8.  So a working flank is a runner
# that can sit at 1/8 with the OTHER neighbour also >= 1/8.
# Measure: at lonely openings, the rank of the flank and the rank of the other neighbour.
from math import gcd
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
def dist(a,b,k):
    x=F(a*(8*k+1), 8*b); f=x-(x.numerator//x.denominator); return min(f,1-f)
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
flank_rank=Counter(); other_rank=Counter(); pair=Counter(); n=0
V=17
for ds in combinations(range(1,V+1),7):
    if gcd(*ds)!=1: continue
    s=sorted(ds)
    for bi,b in enumerate(s):
        for k in range(b):
            if not all(clear(a,b,k) for a in ds): continue
            n+=1
            flank_rank[bi]+=1
            # the OTHER neighbour = the non-flank runner at minimum circle distance
            o=min(((dist(a,b,k), i) for i,a in enumerate(s) if a!=b))
            other_rank[o[1]]+=1
            pair[(bi,o[1])]+=1
print(f"lonely openings examined: {n}")
print(f"  flank rank (0=smallest..6=largest): {dict(sorted(flank_rank.items()))}")
print(f"  other-neighbour rank              : {dict(sorted(other_rank.items()))}")
print()
print("  most common (flank rank, other-neighbour rank) pairs:")
for (a,b),c in pair.most_common(8):
    print(f"     flank rank {a}, neighbour rank {b}: {c}")
print()
# THE KEY QUESTION for (ii): for each SET, are the working flanks confined to high ranks?
lowonly=0; tot=0; dist_wf=Counter()
for ds in combinations(range(1,V+1),7):
    if gcd(*ds)!=1: continue
    s=sorted(ds); tot+=1
    wf=[i for i in range(7) if any(all(clear(a,s[i],k) for a in ds) for k in range(s[i]))]
    dist_wf[min(wf)]+=1
    if max(wf)<4: lowonly+=1
print(f"  sets whose working flanks are ALL below rank 4: {lowonly}/{tot}")
print(f"  distribution of the LOWEST working rank: {dict(sorted(dist_wf.items()))}")
