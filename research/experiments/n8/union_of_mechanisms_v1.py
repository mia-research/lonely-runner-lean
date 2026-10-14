"""Do the PROVED mechanisms, applied across all seven generator choices, cover everything?
M1  all moduli >= 10 at generator s_k        -> DivisorOrder6 (order-6 real witness, rounded)
M2  all moduli <=  9 at s_k, and some q in [L(s_k),U(s_k)] with q = 1 mod lcm(moduli)
                                              -> SmallModuli.clear_one at every modulus
M4  <= 6 distinct readings                    -> CardSix (order-7, margin 1/7 > 1/8)
Report which profiles NO proved mechanism certifies."""
from math import gcd, lcm
from functools import reduce
import random
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
        if min(mo)>=10: return f"M1(k={sk})"
        if max(mo)<=9:
            P=reduce(lcm,mo)
            lo,hi=L(sk),U(sk)
            start=lo+((1-lo)%P)
            if start<=hi: return f"M2(k={sk})"
    return None
def has_witness(ss):
    for sk in ss:
        for q in range(L(sk),U(sk)+1):
            A=8*q+1
            if all(not blocks(si,A,sk) for si in ss): return True
    return False
random.seed(19)
from collections import Counter
for name,gen in (("divisor-closed", None), ("general integer", "gen")):
    cnt=Counter(); tot=0; uncert=[]
    while tot<6000:
        if gen is None:
            m=random.choice([48,72,96,120,144,240,360,480,720,840,1440,2520])
            divs=[d for d in range(1,m+1) if m%d==0]
            if len(divs)<7: continue
            ss=sorted(set([1,m]+random.sample(divs,5)))
        else:
            ss=sorted(set([1]+random.sample(range(2,60),6)))
        if len(ss)!=7: continue
        tot+=1
        c=certifies(ss)
        cnt["certified" if c else "NOT certified"]+=1
        if c: cnt[c.split("(")[0]]+=1
        elif len(uncert)<5: uncert.append(ss)
    print(f"{name}: {tot} profiles")
    print(f"   certified by a proved mechanism: {100*cnt['certified']/tot:6.2f}%  "
          f"(M1 {cnt['M1']}, M2 {cnt['M2']}, M4 {cnt['M4']})")
    print(f"   NOT certified: {100*cnt['NOT certified']/tot:6.2f}%")
    for x in uncert:
        print(f"      {x}   has a witness anyway: {has_witness(x)}")
