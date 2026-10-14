import random
from math import gcd
from collections import Counter
def inway(d,P,Q):
    r=(d*P)%Q; return 8*min(r,Q-r)<Q
def lonely(ds,P,Q):
    for d in ds:
        r=(d*P)%Q
        if 8*min(r,Q-r)<Q: return False
    return True
def nextop(d,P,Q):
    num=8*d*P-Q; den=8*Q; k=-((-num)//den); g=gcd(8*k+1,8*d); return ((8*k+1)//g,(8*d)//g)
def move(ds,P,Q):
    bP,bQ=P,Q
    for d in ds:
        if inway(d,P,Q):
            nP,nQ=nextop(d,P,Q)
            if nP*bQ>bP*nQ: bP,bQ=nP,nQ
    return bP,bQ
def cascade(ds,cap=2000):
    m=min(ds); P,Q=1,8*m; g=gcd(P,Q); P,Q=P//g,Q//g; mv=0
    while mv<cap:
        P2,Q2=move(ds,P,Q)
        if (P2,Q2)==(P,Q): return mv
        P,Q=P2,Q2; mv+=1
    return None
def primitive(s):
    g=0
    for x in s: g=gcd(g,x)
    return g==1

# ---------- DOOR 3: the gap frame ----------
print("=== DOOR 3: '8 gaps, subject lonely iff its TWO adjacent gaps >= 1/8' ===")
random.seed(3); bad=0; checked=0; tight=0
for _ in range(60000):
    v=[random.randint(-60,60) for _ in range(8)]
    if len(set(v))<8: continue
    A=random.randint(1,500); B=random.randint(1,211)
    k=random.randrange(8)
    pos=sorted(((vi*A)%B, i) for i,vi in enumerate(v))
    if len({p for p,_ in pos})<8: continue
    gaps=[]
    for a in range(8):
        b=(a+1)%8
        g=pos[b][0]-pos[a][0]
        if b==0: g+=B
        gaps.append((g,pos[a][1],pos[b][1]))
    assert sum(g for g,_,_ in gaps)==B          # EIGHT gaps, summing to the whole circle
    adj=[g for g,a,b in gaps if a==k or b==k]
    gap_says = (len(adj)==2 and 8*min(adj)>=B)
    lon = all(8*min((( (v[i]-v[k])*A)%B), B-(((v[i]-v[k])*A)%B))>=B for i in range(8) if i!=k)
    checked+=1
    if gap_says!=lon: bad+=1
    if lon and 8*min(adj)==B: tight+=1
print(f"  instants checked {checked};  disagreements: {bad};  exactly-tight lonely cases: {tight}")
print(f"  (the 8-gaps-sum-to-1 identity was asserted on every one of the {checked})")

# ---------- DOOR 5: how far down the ranks must you go? ----------
print()
print("=== DOOR 5: best available flank rank, 1 = LARGEST disparity ===")
random.seed(23)
best=Counter(); worstcase=(0,None); tested=0; nolonely=0
def ranks_for(s):
    srt=sorted(s,reverse=True); out=[]
    for e in s:
        for j in range(e):
            P,Q=8*j+1,8*e; g=gcd(P,Q)
            if lonely(list(s),P//g,Q//g): out.append(srt.index(e)+1); break
    return out
pools=[]
for hi in (20,30,45,70):
    seen=set()
    for _ in range(9000):
        s=tuple(sorted(random.sample(range(1,hi+1),7)))
        if s in seen or not primitive(s): continue
        seen.add(s); pools.append(s)
# targeted: near-AP and tight configurations, where TLF is most likely to be stressed
for a in range(1,40):
    for d in range(1,25):
        s=tuple(sorted(a+d*i for i in range(7)))
        if primitive(s): pools.append(s)
for s in pools:
    r=ranks_for(s)
    tested+=1
    if not r: nolonely+=1; print("   NO lonely opening j<e at any flank:",s); continue
    b=min(r); best[b]+=1
    if b>worstcase[0]: worstcase=(b,s)
print(f"  sets tested: {tested}   (no lonely opening anywhere: {nolonely})")
print(f"  distribution of the BEST available rank: {dict(sorted(best.items()))}")
print(f"  deepest rank ever required: {worstcase[0]}  at {worstcase[1]}")
print(f"  -> 'three largest' holds on this sample iff the deepest is <= 3")
