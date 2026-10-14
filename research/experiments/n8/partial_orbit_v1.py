"""Full closure is not needed for |S| >= 2 -- ONE surviving orbit suffices.
Is there always a solution q with m-q also a solution (or m-1-q)?"""
from itertools import combinations
from collections import Counter

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def ok(q,m,bs): return all(I(b)[0] <= q%b <= I(b)[1] for b in bs+[m])
def good(b): return b % 8 not in (0,1)

tot=0; c0=0; c1=0; either=0; neither=[]
cat=Counter()
for m in range(24, 240):
    ds=[d for d in range(2,m) if m%d==0]
    if len(ds)<5: continue
    for c5 in combinations(ds,5):
        bs=sorted(c5); allb=bs+[m]
        S=set(q for q in range(m) if ok(q,m,bs))
        if not S: continue
        tot+=1
        ng=sum(1 for b in allb if good(b))
        k='all good' if ng==len(allb) else ('all bad' if ng==0 else 'mixed')
        cat[k]+=1
        h0 = any((m-q)%m in S and (m-q)%m != q for q in S)
        h1 = any((m-1-q)%m in S and (m-1-q)%m != q for q in S)
        c0 += h0; c1 += h1
        if h0 or h1: either += 1
        elif len(neither) < 5: neither.append((m,bs,sorted(S)))
print(f"all profiles with a witness : {tot:,}   ({dict(cat)})\n")
print(f"  some q with m-q also a solution, and distinct   : {c0:,}  ({100*c0/tot:.2f}%)")
print(f"  some q with m-1-q also a solution, and distinct : {c1:,}  ({100*c1/tot:.2f}%)")
print(f"  at least one of the two                        : {either:,}  ({100*either/tot:.2f}%)")
if neither:
    print(f"\n  profiles with NEITHER surviving orbit:")
    for m,bs,S in neither: print(f"     m={m} b={bs}  S={S[:8]}")
else:
    print(f"\n  => every profile has a surviving reflection orbit: |S| >= 2 follows for ALL.")
