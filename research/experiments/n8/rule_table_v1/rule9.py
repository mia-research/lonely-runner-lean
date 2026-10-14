# Binding case for the triple rule: sets with only ONE working flank.  Which rank is it?
# If it can be rank 0..3, the triple (4,5,6) would fail there -- so this is the real test.
from math import gcd
from itertools import combinations
from collections import Counter
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def works(ds,b):
    for k in range(b):
        if all(clear(a,b,k) for a in ds): return True
    return False
for V in (17, 20):
    ranks=Counter(); one=[]; n=0
    for ds in combinations(range(1,V+1),7):
        if gcd(*ds)!=1: continue
        n+=1
        s=sorted(ds)
        w=[i for i in range(7) if works(ds,s[i])]
        ranks[len(w)] += 1
        if len(w)==1: one.append((ds,w[0]))
    print(f"[1,{V}] {n} sets.  distribution of #working flanks: {dict(sorted(ranks.items()))}")
    if one:
        rc=Counter(r for _,r in one)
        print(f"   sets with exactly ONE working flank: {len(one)};  its rank: {dict(sorted(rc.items()))}")
        print(f"   examples: {[(d,r) for d,r in one[:4]]}")
        lo=[x for x in one if x[1]<4]
        print(f"   any with the single working flank at rank < 4 (would break the triple): {len(lo)}")
    # also: what is the LOWEST rank that is ever the unique working flank
    print()
