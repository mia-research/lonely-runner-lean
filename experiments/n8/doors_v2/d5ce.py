from math import gcd
from collections import Counter
import random
def lonely(ds,P,Q):
    for d in ds:
        r=(d*P)%Q
        if 8*min(r,Q-r)<Q: return False
    return True
def ranks_for(s):
    srt=sorted(s,reverse=True); out={}
    for e in s:
        for j in range(e):
            P,Q=8*j+1,8*e; g=gcd(P,Q)
            if lonely(list(s),P//g,Q//g): out[srt.index(e)+1]=(e,j); break
    return out
def primitive(s):
    g=0
    for x in s: g=gcd(g,x)
    return g==1
random.seed(23); seen=set(); r2=[]; r3=[]
pools=[]
for hi in (20,30,45,70):
    for _ in range(9000):
        s=tuple(sorted(random.sample(range(1,hi+1),7)))
        if s in seen or not primitive(s): continue
        seen.add(s); pools.append(s)
for a in range(1,40):
    for d in range(1,25):
        s=tuple(sorted(a+d*i for i in range(7)))
        if primitive(s): pools.append(s)
for s in pools:
    r=ranks_for(s)
    if not r: continue
    b=min(r)
    if b==2 and len(r2)<4: r2.append((s,r[b]))
    if b==3: r3.append((s,r[b]))
print("LARGEST flank fails (best rank 2) -- examples (set, (flank e, lap j)):")
for s,x in r2: print("   ",s,"->",x)
print(f"best rank 3 cases: {len(r3)}")
for s,x in r3: print("   ",s,"->",x)
