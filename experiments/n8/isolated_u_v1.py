"""The 2.7%: profiles whose admissible u-set has no two consecutive members.
These are not failures -- the set is never empty. An isolated u means BOTH neighbours are
blocked, i.e. a doubly-tight witness. Find them and read the mechanism."""
from math import gcd, lcm
from functools import reduce
from collections import Counter
import random
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def clear(b,q): return L(b) <= q % b <= U(b)
def blockers(bs,q): return [b for b in bs if not clear(b,q)]
random.seed(31)
iso=[]; tot=0; runs=Counter()
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
    ok=[u for u in range(M) if all(clear(b,2*u+1) for b in bs)]
    best=0;cur=0
    for u in range(M):
        if all(clear(b,2*u+1) for b in bs): cur+=1; best=max(best,cur)
        else: cur=0
    runs[min(best,5)]+=1
    if best==1 and ok:
        u0=ok[0]
        iso.append((bs, M, u0,
                    blockers(bs,2*(u0-1)+1), blockers(bs,2*(u0+1)+1)))
    if tot>=2000: break
print(f"profiles with b=2 present: {tot}")
print(f"   longest-run distribution (5 = '>=5'): {dict(sorted(runs.items()))}")
print(f"   isolated-only (longest run = 1): {len(iso)} = {100*len(iso)/tot:.2f}%")
print(f"   EMPTY clear set: {runs[0]}  <- existence is never the issue")
print()
print("   what blocks the two neighbours of an isolated witness?")
c=Counter()
for bs,M,u0,lo,hi in iso:
    c[(tuple(lo),tuple(hi))]+=1
for k,v in c.most_common(8):
    print(f"      left blocked by {k[0]}, right by {k[1]}: {v}")
print()
print("   moduli sets of the isolated cases:")
for bs,M,u0,lo,hi in iso[:8]:
    print(f"      bs={bs} M={M} u={u0}  left-blocker {lo}  right-blocker {hi}")
