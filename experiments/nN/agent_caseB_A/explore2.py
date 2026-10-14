from core import *
from collections import Counter
from fractions import Fraction as F
def L2(ns):
    for i in range(1,7):
        if 9*ns[i-1] <= 7*ns[i] and 3*ns[6] <= 5*ns[i]: return i
    return None
sets=list(integer_band_sets(24))
res=[ns for ns in sets if L2(ns) is None]
print("residual after L2:", len(res), "of", len(sets))
pat=Counter(); works=Counter()
for ns in res:
    g=tuple(int(9*ns[i-1]<=7*ns[i]) for i in range(1,7))
    pat[g]+=1
    w=[(e,K) for R,e,K in candidates(ns) if block_ok(ns,e,K)]
    for x in set(w): works[x]+=1
print("gap>=9/7 pattern (positions1..6):", pat.most_common())
print("blocks working in residual:", sorted(works.items(), key=lambda t:-t[1])[:40])
# greedy cover
W={ns:set((e,K) for R,e,K in candidates(ns) if block_ok(ns,e,K)) for ns in res}
left=set(res); chosen=[]
while left:
    c=Counter()
    for ns in left:
        for x in W[ns]: c[x]+=1
    b,v=c.most_common(1)[0]; chosen.append((b,v)); left={ns for ns in left if b not in W[ns]}
print("greedy:", chosen)
