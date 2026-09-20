"""The order-6 band implies clearing at EVERY modulus except b in {2,3,8,9}, where it admits
exactly one blocked residue each: 0, 0, 7, 8. Confirm over a wide range, then measure how hard
those four conditions are to satisfy inside the band."""
from math import gcd, lcm
from functools import reduce
import random
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def bandonly(b): return [r for r in range(b) if (b-3 <= 6*r <= 5*b+3) and not (L(b) <= r <= U(b))]
bad=[(b,bandonly(b)) for b in range(2,4001) if bandonly(b)]
print(f"moduli b in 2..4000 where the band admits a blocked residue: {[x[0] for x in bad]}")
print(f"   and the residues are: {dict(bad)}")
print(f"   exactly one residue at each: {all(len(v)==1 for _,v in bad)}")
print()
print("so the reduced obligation is FOUR named residue conditions, when those moduli occur:")
print("   q != 0 (mod 2),  q != 0 (mod 3),  q != 7 (mod 8),  q != 8 (mod 9)")
allowed=[q for q in range(72) if q%2 and q%3 and q%8!=7 and q%9!=8]
print(f"   allowed q mod 72: {len(allowed)}/72 = {100*len(allowed)/72:.1f}%  e.g. {allowed[:8]}")
print()
print("how often does a profile even CONTAIN one of 2,3,8,9 as a modulus?")
random.seed(5)
from collections import Counter
cnt=Counter(); tot=0
for _ in range(200000):
    m=random.choice([48,72,96,120,144,240,360,480,720,840,1440,2520])
    divs=[d for d in range(1,m+1) if m%d==0]
    if len(divs)<7: continue
    ss=sorted(set([1,m]+random.sample(divs,5)))
    if len(ss)!=7: continue
    tot+=1
    hit=False
    for sk in ss:
        mo=set(sk//gcd(si,sk) for si in ss if si!=sk)
        if mo & {2,3,8,9}: hit=True
    cnt["has one of 2,3,8,9 at every generator" if hit else "some generator avoids all four"]+=1
    if tot>=8000: break
for k,v in cnt.items(): print(f"   {k}: {100*v/tot:.2f}%")
