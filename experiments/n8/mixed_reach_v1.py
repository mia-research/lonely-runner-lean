"""Reach of the DE-RESTRICTED theorem: no homogeneity.
  b >= 10 : q in the 1/6 band  ->  clear          (DivisorOrder6.clear_of_order6, per modulus)
  b <=  9 : q mod b in [L(b),U(b)] directly       (no band needed; blocked set is tiny)
Ask for a single q meeting BOTH. How much of the divisor-closed space does that cover, against
the 14% the homogeneity-bound theorems reach?"""
from math import lcm
from functools import reduce
import random
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def band(b,q): r=q%b; return b-3 <= 6*r and 6*r <= 5*b+3
def clear1(b,q): return L(b) <= q % b <= U(b)
def mixed_ok(bs,q):
    return all((band(b,q) if b>=10 else clear1(b,q)) for b in bs)
def clears(bs,q): return all(clear1(b,q) for b in bs)
random.seed(37)
tot=0; reach=0; sound=0; old=0
for _ in range(200000):
    m=random.choice([48,72,96,120,144,192,240,288,360,480,720,840,960,1440,2520])
    divs=[d for d in range(2,m+1) if m%d==0]
    if len(divs)<5: continue
    bs=sorted(random.sample(divs,5))
    M=reduce(lcm,bs)
    if M>300000: continue
    tot+=1
    if min(bs)>=10 or max(bs)<=9: old+=1          # what the homogeneity theorems reach
    hit=None
    for q in range(M):
        if mixed_ok(bs,q): hit=q; break
    if hit is not None:
        reach+=1
        if clears(bs,hit): sound+=1
    if tot>=8000: break
print(f"divisor-closed profiles sampled: {tot}")
print(f"   reached by the HOMOGENEITY-bound theorems (all>=10 or all<=9): {100*old/tot:6.2f}%")
print(f"   reached by the DE-RESTRICTED mixed condition:                  {100*reach/tot:6.2f}%")
print(f"   and where it fires, q really clears:  {sound}/{reach} "
      f"{'ALL' if sound==reach else 'MISMATCH'}")
