"""CORRECTED. M3 in the previous run was a bounded exhaustive search, not a theorem -- it just
checked 9 candidates directly. Drop it. Report coverage by genuinely PROVED mechanisms only,
then measure the bounded-search fact separately, as the lead it is."""
from math import gcd, lcm
from functools import reduce
import random
from collections import Counter
import statistics as st
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def blocks(si,A,sk):
    M=8*sk; r=(si*A)%M; return min(r,M-r)<sk
def moduli(ss,sk): return [sk//gcd(si,sk) for si in ss if si!=sk and sk//gcd(si,sk)>1]
def certifies(ss):
    if len(set(ss))<=6: return "M4"
    for sk in ss:
        mo=moduli(ss,sk)
        if not mo: continue
        if min(mo)>=10: return "M1"
        if max(mo)<=9:
            P=reduce(lcm,mo); s=L(sk)+((1-L(sk))%P)
            if s<=U(sk): return "M2"
    for sk in ss:
        Lc=reduce(lcm,[sk//gcd(si,sk) for si in ss if si!=sk] or [1]); A=8*Lc-7
        if L(sk)<=(A-1)//8<=U(sk) and all(not blocks(si,A,sk) for si in ss): return "M5"
    return None
def min_steps(ss):
    """over all generators, the fewest steps above L(s_k) at which a clear candidate appears"""
    best=None
    for sk in ss:
        for q in range(L(sk),U(sk)+1):
            if all(not blocks(si,8*q+1,sk) for si in ss):
                d=q-L(sk)
                if best is None or d<best: best=d
                break
    return best
random.seed(23)
for name in ("divisor-closed","general integer"):
    cnt=Counter(); tot=0; steps=[]
    while tot<6000:
        if name=="divisor-closed":
            m=random.choice([48,72,96,120,144,240,360,480,720,840,1440,2520])
            divs=[d for d in range(1,m+1) if m%d==0]
            if len(divs)<7: continue
            ss=sorted(set([1,m]+random.sample(divs,5)))
        else:
            ss=sorted(set([1]+random.sample(range(2,60),6)))
        if len(ss)!=7: continue
        tot+=1
        cnt[certifies(ss) or "NONE"]+=1
        s=min_steps(ss)
        if s is not None: steps.append(s)
    cov=100*(tot-cnt["NONE"])/tot
    print(f"{name}: {tot} profiles")
    print(f"   certified by PROVED mechanisms (M1,M2,M4,M5): {cov:.2f}%   {dict(cnt)}")
    print(f"   [LEAD, not a theorem] fewest steps above L(s_k) over the 7 generators:")
    print(f"      min {min(steps)}  median {st.median(steps):.0f}  mean {st.mean(steps):.2f}  MAX {max(steps)}")
    print(f"      within 8 steps: {100*sum(1 for s in steps if s<=8)/len(steps):.2f}%   "
          f"profiles with no witness at all: {tot-len(steps)}")
