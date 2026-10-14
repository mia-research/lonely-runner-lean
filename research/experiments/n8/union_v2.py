"""All PROVED mechanisms, across all seven generators.
M1 all moduli >= 10        -> DivisorOrder6
M2 all moduli <= 9 + a q=1 mod lcm in band -> SmallModuli.clear_one
M3 FirstLap window: some A=8q+1 in band with s_k <= s_i*A' ... (ratio-7 reach of one candidate)
M5 the -7 opening: A = 8L-7 clears iff no blocker has dist(7*s_i, 8*s_k*Z) < s_k
M4 <= 6 distinct readings  -> CardSix"""
from math import gcd, lcm
from functools import reduce
import random
from collections import Counter
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
    for sk in ss:                                   # M5: the -7 opening
        Lc=reduce(lcm,[sk//gcd(si,sk) for si in ss if si!=sk] or [1])
        A=8*Lc-7
        if L(sk)<=(A-1)//8<=U(sk) and all(not blocks(si,A,sk) for si in ss): return "M5"
    for sk in ss:                                   # M3: one candidate, ratio-7 reach
        others=[si for si in ss if si!=sk]
        lo=max(L(b) for b in [sk//gcd(si,sk) for si in others] or [1])
        for q in range(L(sk), min(U(sk), L(sk)+8)+1):
            A=8*q+1
            if all(sk <= (si*A) % (8*sk) <= 7*sk for si in others): return "M3"
    return None
random.seed(23)
for name in ("divisor-closed","general integer"):
    cnt=Counter(); tot=0; res=[]
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
        c=certifies(ss); cnt[c or "NONE"]+=1
        if not c and len(res)<6: res.append(ss)
    cov=100*(tot-cnt["NONE"])/tot
    print(f"{name}: {tot} profiles -- certified {cov:.2f}%   {dict(cnt)}")
    for x in res: print(f"      residual: {x}")
