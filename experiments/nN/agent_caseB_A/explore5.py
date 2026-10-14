from core import *
from collections import Counter
import sys
def types(ns):
    out=set()
    for R,e,K in candidates(ns):
        if block_ok(ns,e,K):
            laps=tuple(((8*K+1)*nd)//(8*ns[e]) for nd in ns)
            out.add((e,K,laps))
    return out
rows=[l.split() for l in open('fine_shapes.txt')]
S=[tuple(map(int,r[:7])) for r in rows]
S+= list(integer_band_sets(24))
T={ns:types(ns) for ns in S}
left=set(S); chosen=[]
while left:
    c=Counter()
    for ns in left:
        for x in T[ns]: c[x]+=1
    b,v=c.most_common(1)[0]; chosen.append((b,v)); left={ns for ns in left if b not in T[ns]}
print("greedy types needed:", len(chosen))
for b,v in chosen: print(v,b)
