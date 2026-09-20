"""How much of the isolated 2.7% is the (5,10) pair, and what causes the rest?"""
from math import lcm, gcd
from functools import reduce
from collections import Counter
import random
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def clr(b,u): return L(b) <= (2*u+1) % b <= U(b)
def isolated(bs):
    M=reduce(lcm,bs)
    A=[u for u in range(M) if all(clr(b,u) for b in bs)]
    S=set(A)
    return bool(A) and not any((u+1)%M in S for u in A), A, M
random.seed(31)
iso=[]; tot=0
for _ in range(120000):
    m=random.choice([24,48,72,96,120,144,240,360,720,840,2520])
    divs=[d for d in range(1,m+1) if m%d==0]
    if len(divs)<7: continue
    ss=sorted(set([1,m]+random.sample(divs,5)))
    if len(ss)!=7: continue
    bs=sorted(set(m//si for si in ss if si!=m and m//si>1))
    if not bs or 2 not in bs: continue
    M=reduce(lcm,bs)
    if M>40000: continue
    tot+=1
    ok,A,MM=isolated(bs)
    if ok: iso.append(bs)
    if tot>=2000: break
print(f"profiles with b=2: {tot};  isolated: {len(iso)} = {100*len(iso)/tot:.2f}%")
have510=[b for b in iso if 5 in b and 10 in b]
print(f"   containing BOTH 5 and 10: {len(have510)} = {100*len(have510)/len(iso):.1f}% of the isolated")
rest=[b for b in iso if not (5 in b and 10 in b)]
print(f"   the rest: {len(rest)}")
c=Counter()
for bs in rest:
    # smallest isolating sub-multiset
    best=None
    for k in (2,3,4):
        from itertools import combinations
        for sub in combinations(bs,k):
            if isolated(list(sub))[0]:
                best=sub; break
        if best: break
    c[best]+=1
print(f"   minimal isolating sub-sets among the rest:")
for k,v in c.most_common(10): print(f"      {k}: {v}")
