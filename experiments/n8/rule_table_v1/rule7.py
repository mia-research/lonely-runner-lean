# Owner: is it the right COMBINATION of flanks?  Test every pair and triple of RANKS
# (0 = smallest .. 6 = largest) exhaustively: does any fixed combination always contain a
# working flank?
from math import gcd
from itertools import combinations
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def works(ds,b):
    return any(all(clear(a,b,k) for a in ds) for k in range(b))
for V in (14, 17):
    sets=[ds for ds in combinations(range(1,V+1),7) if gcd(*ds)==1]
    W=[]
    for ds in sets:
        s=sorted(ds)
        W.append(tuple(works(ds,b) for b in s))
    n=len(W)
    print(f"[1,{V}]  {n} primitive sets")
    # single ranks
    single=[(sum(1 for w in W if w[i])/n, i) for i in range(7)]
    single.sort(reverse=True)
    print(f"   best single rank : rank {single[0][1]} covers {single[0][0]:.4f}")
    # pairs
    best=[]
    for i,j in combinations(range(7),2):
        c=sum(1 for w in W if w[i] or w[j])/n
        best.append((c,(i,j)))
    best.sort(reverse=True)
    print(f"   best pairs       : " + ", ".join(f"{p}={c:.4f}" for c,p in best[:3]))
    full=[p for c,p in best if c==1.0]
    print(f"   pairs covering ALL sets: {full if full else 'NONE'}")
    # triples
    bt=[]
    for t in combinations(range(7),3):
        c=sum(1 for w in W if any(w[i] for i in t))/n
        bt.append((c,t))
    bt.sort(reverse=True)
    print(f"   best triples     : " + ", ".join(f"{t}={c:.4f}" for c,t in bt[:3]))
    fullt=[t for c,t in bt if c==1.0]
    print(f"   triples covering ALL sets: {fullt if fullt else 'NONE'}")
    # how many ranks are needed at worst?
    need=max(min(i for i in range(7) if w[i]) for w in W)
    print(f"   worst case: the smallest working rank is as high as {need}")
    nw=[sum(w) for w in W]
    print(f"   number of working flanks per set: min {min(nw)}  median {sorted(nw)[n//2]}")
    print()
