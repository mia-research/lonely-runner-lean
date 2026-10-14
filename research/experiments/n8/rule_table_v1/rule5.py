# R1 (nearest) or R2 (largest) leaves 54 sets uncovered on [1,14].  What serves them?
from math import gcd
from itertools import combinations
def clear(a,b,k):
    s=a%8; q=a//8; c=(a*k+q)%b
    return (b-s) <= 8*c <= (7*b-s)
def firstk(ds,b):
    for k in range(b):
        if all(clear(a,b,k) for a in ds): return k
    return None
def works(ds,b): return firstk(ds,b) is not None
miss=[]
for ds in combinations(range(1,15),7):
    if gcd(*ds)!=1: continue
    if not (works(ds,min(ds)) or works(ds,max(ds))): miss.append(ds)
print(f"uncovered by R1 or R2 on [1,14]: {len(miss)}")
print(f"  all contain 7 and 8? {all(7 in d and 8 in d for d in miss)}")
print(f"  all contain a multiple of 8? {all(any(a%8==0 for a in d) for d in miss)}")
print()
# which flanks DO work for them, and is there a rule?
from collections import Counter
pos=Counter(); vals=Counter()
for ds in miss:
    good=[b for b in ds if works(ds,b)]
    for b in good:
        pos[sorted(ds).index(b)] += 1
        vals[b] += 1
    if not good: print(f"   NO FLANK WORKS for {ds}")
print(f"  which rank of flank works (0=smallest .. 6=largest): {dict(sorted(pos.items()))}")
print(f"  which flank VALUES work: {dict(sorted(vals.items()))}")
print()
# candidate R3: the largest flank NOT divisible by 8?  or the second largest?
def r3a(ds): 
    c=[b for b in ds if b%8!=0]
    return max(c) if c else max(ds)
def r3b(ds): return sorted(ds)[-2]
def r3c(ds):
    c=[b for b in ds if b%8!=0 and b%2==1]
    return max(c) if c else max(ds)
for name,f in (("largest not divisible by 8", r3a), ("second largest", r3b), ("largest odd, not div by 8", r3c)):
    ok=sum(1 for ds in miss if works(ds,f(ds)))
    print(f"  R3 = {name:28s}: covers {ok}/{len(miss)}")
print()
# full three-rule table, exhaustive
for V in (14, 17):
    cnt=0; cov=0; left=[]
    for ds in combinations(range(1,V+1),7):
        if gcd(*ds)!=1: continue
        cnt+=1
        if works(ds,min(ds)) or works(ds,max(ds)) or works(ds,r3a(ds)): cov+=1
        else: left.append(ds)
    print(f"  [1,{V}] R1 or R2 or R3(largest not div by 8): {cov}/{cnt} = {cov/cnt:.4f};  left {len(left)}")
    if left: print(f"      {left[:5]}")
