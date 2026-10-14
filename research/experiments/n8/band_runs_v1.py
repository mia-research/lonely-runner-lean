"""How close is the band intersection to making the four exclusions free?
15 of 72 residues mod 72 satisfy all four. If the intersection of the bands contains 72
consecutive integers it certainly contains an allowed one. Measure the longest run."""
from math import gcd, lcm
from functools import reduce
import random, statistics as st
def band(b,q): r=q%b; return b-3 <= 6*r <= 5*b+3
def ok4(q,bs):
    return ((2 not in bs or q%2) and (3 not in bs or q%3)
            and (8 not in bs or q%8!=7) and (9 not in bs or q%9!=8))
random.seed(29)
runs=[]; hasgood=0; tot=0; nowitness=0
for _ in range(120000):
    m=random.choice([48,72,96,120,144,240,360,480,720,840,1440,2520])
    divs=[d for d in range(1,m+1) if m%d==0]
    if len(divs)<7: continue
    ss=sorted(set([1,m]+random.sample(divs,5)))
    if len(ss)!=7: continue
    sk=max(ss)
    bs=sorted(set(sk//gcd(si,sk) for si in ss if si!=sk and sk//gcd(si,sk)>1))
    if not bs: continue
    M=reduce(lcm,bs)
    if M>60000: continue
    tot+=1
    best=0; cur=0; good=False
    for q in range(M):
        if all(band(b,q) for b in bs):
            cur+=1; best=max(best,cur)
            if ok4(q,bs): good=True
        else: cur=0
    runs.append(best)
    if good: hasgood+=1
    else: nowitness+=1
    if tot>=4000: break
print(f"profiles {tot}")
print(f"   longest run of consecutive integers in the band intersection:")
print(f"      min {min(runs)}  median {st.median(runs):.0f}  mean {st.mean(runs):.1f}  max {max(runs)}")
print(f"      runs >= 72 (would make the four exclusions free): "
      f"{100*sum(1 for r in runs if r>=72)/len(runs):.2f}%")
print(f"   band intersection contains a q satisfying all four exclusions: "
      f"{100*hasgood/tot:.2f}%   (none: {nowitness})")
