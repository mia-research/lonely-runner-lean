"""We have SEVEN generating readings. DivisorOrder6 closes a profile when all moduli are >= 10;
SmallModuli closes it when all are <= 9. The modulus at blocker s_i under generator s_k is
q_i = s_k / gcd(s_i, s_k) -- it CHANGES with k. We only need ONE k to be homogeneous.
Is there always such a k?"""
from math import gcd
from functools import reduce
import random
def moduli(ss, sk):
    return [sk//gcd(si,sk) for si in ss if si != sk and sk//gcd(si,sk) > 1]
def homogeneous_k(ss):
    """generators k for which every modulus is >= 10, or every modulus is <= 9"""
    big=[]; small=[]
    for sk in ss:
        m=moduli(ss,sk)
        if not m: continue
        if min(m)>=10: big.append(sk)
        if max(m)<=9: small.append(sk)
    return big, small
random.seed(3)
print("divisor-closed profiles: is some generator homogeneous?")
for M in ([48,72,96,120,144,240,360,480,720,840,1440,2520],):
    tot=0; hasbig=0; hassmall=0; haseither=0; neither=[]
    for _ in range(200000):
        m=random.choice(M)
        divs=[d for d in range(1,m+1) if m%d==0]
        if len(divs)<7: continue
        ss=sorted(set([1,m]+random.sample(divs,5)))
        if len(ss)!=7: continue
        tot+=1
        big,small=homogeneous_k(ss)
        if big: hasbig+=1
        if small: hassmall+=1
        if big or small: haseither+=1
        elif len(neither)<6: neither.append(ss)
        if tot>=8000: break
    print(f"   profiles {tot}")
    print(f"      some generator with ALL moduli >= 10 : {100*hasbig/tot:6.2f}%")
    print(f"      some generator with ALL moduli <=  9 : {100*hassmall/tot:6.2f}%")
    print(f"      either                               : {100*haseither/tot:6.2f}%")
    for x in neither: print(f"         neither: {x}")
print()
print("general (non-divisor-closed) integer profiles:")
tot=0; haseither=0; neither=[]
for _ in range(60000):
    ss=sorted(set([1]+random.sample(range(2,60),6)))
    if len(ss)!=7: continue
    tot+=1
    big,small=homogeneous_k(ss)
    if big or small: haseither+=1
    elif len(neither)<4: neither.append(ss)
print(f"   profiles {tot}: some homogeneous generator {100*haseither/tot:6.2f}%")
for x in neither: print(f"      neither: {x}")
