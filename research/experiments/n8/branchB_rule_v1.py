"""Branch B (some reading has 8 | s): L(m) is pinned to 0 at every collider.
Which explicit candidate lands the witness? Test formulas, find the rule."""
from math import lcm, gcd
from functools import reduce
import random
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def clears(bs,q): return all(L(b) <= q % b <= U(b) for b in bs)
random.seed(13)
profs=[]
for _ in range(120000):
    m=random.choice([48,72,96,120,144,192,240,288,360,480,720,840,960,1440,2520])
    divs=[d for d in range(2,m+1) if m%d==0]
    if len(divs)<5: continue
    bs=sorted(random.sample(divs,5))
    if not any((m//b)%8==0 for b in bs): continue
    profs.append((m,bs))
    if len(profs)>=20000: break
print(f"Branch B divisor-closed profiles: {len(profs)}")
def mid(bs): 
    bm=max(bs); return (L(bm)+U(bm))//2
cands={
 "L(m)":                lambda m,bs: L(m),
 "L(m)+1":              lambda m,bs: L(m)+1,
 "L(m)+L(b*) largest collider": lambda m,bs: L(m)+L(max([b for b in bs if (m//b)%8==0])),
 "L(m)+max_b L(b)":     lambda m,bs: L(m)+max(L(b) for b in bs),
 "L(b_max)":            lambda m,bs: L(max(bs)),
 "L(b_max)+1":          lambda m,bs: L(max(bs))+1,
 "mid of b_max window": lambda m,bs: mid(bs),
 "ceil(m/4)":           lambda m,bs: -((-m)//4),
 "ceil(3m/8)":          lambda m,bs: -((-3*m)//8),
 "sum L(b)":            lambda m,bs: sum(L(b) for b in bs),
 "lcm-based: L(M) M=lcm": lambda m,bs: L(reduce(lcm,bs)),
}
for name,f in cands.items():
    hit=sum(1 for m,bs in profs if clears(bs,f(m,bs)))
    print(f"   {name:30s} {100*hit/len(profs):6.2f}%")
