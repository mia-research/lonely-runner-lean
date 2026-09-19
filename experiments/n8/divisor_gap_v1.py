"""After DivisorOrder6 (all b >= 10) and SmallModuli (all b <= 9), what is left?
Also: a single q reaches the ratio-7 window (8q+1)/7 <= b <= 8q+1, so profiles spanning at
most a factor of 7 need no witness argument either."""
from math import gcd, lcm
from functools import reduce
import random
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def single_q(bs):
    """an integer q < min(bs) with b <= 8q+1 <= 7b for every b, or None"""
    lo=max(L(b) for b in bs); hi=min(U(b) for b in bs)
    for q in range(max(1,lo), hi+1):
        if q < min(bs) and all(b <= 8*q+1 <= 7*b for b in bs): return q
    return None
def clears(bs,q): return all(L(b) <= q % b <= U(b) for b in bs)
random.seed(9)
cats={'all <= 9 (q=1, PROVED)':0,'all >= 10 (order-6, PROVED)':0,
      'mixed, one-q window (PROVED)':0,'mixed, OPEN':0}
openex=[]; n=0
for _ in range(60000):
    m=random.choice([24,36,48,60,72,96,120,144,180,240,360,504,720,840])
    divs=[d for d in range(2,m+1) if m%d==0]
    if len(divs)<5: continue
    bs=sorted(random.sample(divs,5)); n+=1
    if max(bs)<=9: cats['all <= 9 (q=1, PROVED)']+=1
    elif min(bs)>=10: cats['all >= 10 (order-6, PROVED)']+=1
    elif single_q(bs) is not None: cats['mixed, one-q window (PROVED)']+=1
    else:
        cats['mixed, OPEN']+=1
        if len(openex)<6: openex.append(bs)
print(f"divisor-closed 5-quotient profiles sampled: {n}")
for k,v in cats.items(): print(f"   {k:34s} {v:7d}  {100*v/n:5.1f}%")
print(f"\n   open examples: {openex}")
print("\n   sanity: q=1 clears every modulus 2..9, and fails from 10")
print(f"      q=1 clears b=2..9 : {all(L(b) <= 1 <= U(b) for b in range(2,10))}")
print(f"      q=1 fails  b=10..40: {all(not (L(b) <= 1 <= U(b)) for b in range(10,41))}")
print("\n   sanity: single-q window really clears, where it fires")
bad=0; tot=0
for _ in range(20000):
    bs=sorted(random.sample(range(2,80),5))
    q=single_q(bs)
    if q is None: continue
    tot+=1
    if not clears(bs,q): bad+=1
print(f"      {tot-bad}/{tot} {'ALL CLEAR' if bad==0 else f'FAILS {bad}'}")
