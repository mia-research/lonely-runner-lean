# Which triples of flank RANKS cover every set?  Is there a common structure (a rank that must
# be present), or is it arbitrary?  Exhaustive.
from math import gcd
from itertools import combinations
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def works(ds,b):
    for k in range(b):
        if all(clear(a,b,k) for a in ds): return True
    return False
for V in (17, 20):
    W=[]
    for ds in combinations(range(1,V+1),7):
        if gcd(*ds)!=1: continue
        s=sorted(ds)
        W.append(tuple(works(ds,b) for b in s))
    n=len(W)
    winners=[]; rows=[]
    for t in combinations(range(7),3):
        c=sum(1 for w in W if any(w[i] for i in t))
        rows.append((c/n,t))
        if c==n: winners.append(t)
    rows.sort(reverse=True)
    print(f"[1,{V}]  {n} sets.  triples covering EVERY set: {len(winners)}")
    print(f"   winners: {winners}")
    print(f"   next best: " + ", ".join(f"{t}={c:.5f}" for c,t in rows[len(winners):len(winners)+4]))
    if winners:
        common=set(range(7))
        for t in winners: common &= set(t)
        print(f"   ranks present in EVERY winning triple: {sorted(common)}")
        from collections import Counter
        cc=Counter(i for t in winners for i in t)
        print(f"   rank frequency among winners: {dict(sorted(cc.items()))}")
    # pairs, for contrast
    pw=[t for t in combinations(range(7),2) if sum(1 for w in W if any(w[i] for i in t))==n]
    print(f"   pairs covering every set: {pw if pw else 'NONE'}")
    print()
