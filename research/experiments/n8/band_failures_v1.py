"""The band+four-exclusions route failed on 2 of 4000 at the largest generator.
Do those profiles clear at another generator, or is the band itself too strict?"""
from math import gcd, lcm
from functools import reduce
import random
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def band(b,q): r=q%b; return b-3 <= 6*r <= 5*b+3
def win(b,q): return L(b) <= q%b <= U(b)
def ok4(q,bs):
    return ((2 not in bs or q%2) and (3 not in bs or q%3)
            and (8 not in bs or q%8!=7) and (9 not in bs or q%9!=8))
def mods(ss,sk): return sorted(set(sk//gcd(si,sk) for si in ss if si!=sk and sk//gcd(si,sk)>1))
random.seed(29)
fails=[]; tot=0
while tot<4000:
    m=random.choice([48,72,96,120,144,240,360,480,720,840,1440,2520])
    divs=[d for d in range(1,m+1) if m%d==0]
    if len(divs)<7: continue
    ss=sorted(set([1,m]+random.sample(divs,5)))
    if len(ss)!=7: continue
    sk=max(ss); bs=mods(ss,sk)
    if not bs: continue
    M=reduce(lcm,bs)
    if M>60000: continue
    tot+=1
    if not any(all(band(b,q) for b in bs) and ok4(q,bs) for q in range(M)):
        fails.append(ss)
print(f"profiles {tot}, band+four failures at the largest generator: {len(fails)}")
for ss in fails:
    print(f"\n  profile {ss}")
    for sk in ss:
        bs=mods(ss,sk)
        if not bs: continue
        M=reduce(lcm,bs)
        if M>200000: print(f"     generator {sk}: moduli {bs} (lcm too large to sweep)"); continue
        bandok=any(all(band(b,q) for b in bs) and ok4(q,bs) for q in range(M))
        winok =any(all(win(b,q) for b in bs) for q in range(M))
        print(f"     generator {sk:5d}: moduli {str(bs):28s} band+four {bandok}   clears {winok}")
