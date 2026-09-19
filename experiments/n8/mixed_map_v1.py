"""Map the mixed case: 13,122 profiles with no reflection centre, yet |S| >= 2 always.
What gives them a second solution?"""
from itertools import combinations
from collections import Counter

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def ok(q,m,bs): return all(I(b)[0] <= q%b <= I(b)[1] for b in bs+[m])
def good(b): return b % 8 not in (0,1)

tot=0; consec=0; runlen=Counter(); minS=Counter(); noconsec=[]
partial=Counter()
for m in range(24, 240):
    ds=[d for d in range(2,m) if m%d==0]
    if len(ds)<5: continue
    for c5 in combinations(ds,5):
        bs=sorted(c5); allb=bs+[m]
        ng=sum(1 for b in allb if good(b))
        if ng==len(allb) or ng==0: continue        # mixed only
        S=sorted(q for q in range(m) if ok(q,m,bs))
        if not S: continue
        tot+=1; minS[len(S)]+=1
        # consecutive pairs?
        runs=[]; cur=1
        for i in range(1,len(S)):
            if S[i]==S[i-1]+1: cur+=1
            else: runs.append(cur); cur=1
        runs.append(cur)
        mx=max(runs); runlen[mx]+=1
        if mx>=2: consec+=1
        elif len(noconsec)<5: noconsec.append((m,bs,S))
        # does the GOOD part alone admit the reflection on S?
        partial[('good moduli', sum(1 for b in allb if good(b)))] += 1
print(f"mixed profiles (no reflection centre) : {tot:,}")
print(f"  |S| distribution (smallest six)     : {dict(sorted(minS.items())[:6])}")
print(f"  S contains two CONSECUTIVE integers : {consec:,}  ({100*consec/tot:.2f}%)")
print(f"  longest run length distribution     : {dict(sorted(runlen.items())[:8])}")
if noconsec:
    print(f"\n  profiles with NO consecutive pair (max run 1):")
    for m,bs,S in noconsec: print(f"     m={m} b={bs}  S={S[:8]}{'...' if len(S)>8 else ''}")
else:
    print(f"\n  every mixed profile has two consecutive solutions -> |S| >= 2 immediately.")
