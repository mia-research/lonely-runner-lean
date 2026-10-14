"""Does q = 1 (mod P) cost anything, P = lcm of the moduli <= 9?
q = 1 mod P gives q mod b' = 1 for every small b', and L(b')=1 for b' <= 9, so ALL small moduli
clear for free. Question: does a witness of that form still exist?"""
from math import lcm
from functools import reduce
import random
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def clears(bs,q): return all(L(b) <= q % b <= U(b) for b in bs)
random.seed(41)
tot=0; any_w=0; cong_w=0; mixed=0; mixed_cong=0
for _ in range(200000):
    m=random.choice([48,72,96,120,144,192,240,288,360,480,720,840,960,1440,2520])
    divs=[d for d in range(2,m+1) if m%d==0]
    if len(divs)<5: continue
    bs=sorted(random.sample(divs,5))
    M=reduce(lcm,bs)
    if M>300000: continue
    small=[b for b in bs if b<=9]; large=[b for b in bs if b>=10]
    tot+=1
    isMixed = bool(small) and bool(large)
    if isMixed: mixed+=1
    P = reduce(lcm, small) if small else 1
    W=[q for q in range(M) if clears(bs,q)]
    if W: any_w+=1
    Wc=[q for q in W if q % P == 1 % P]
    if Wc:
        cong_w+=1
        if isMixed: mixed_cong+=1
    if tot>=6000: break
print(f"divisor-closed profiles: {tot}  (mixed: {mixed})")
print(f"   a witness exists at all:                  {100*any_w/tot:6.2f}%")
print(f"   a witness with q = 1 (mod P) exists:      {100*cong_w/tot:6.2f}%")
print(f"   of the MIXED ones, q = 1 (mod P) witness: {100*mixed_cong/mixed:6.2f}%")
print()
print("   so the small moduli can be discharged by one congruence, at cost:")
print(f"   {100*(any_w-cong_w)/tot:.2f} points of profiles lose their witness under it")
