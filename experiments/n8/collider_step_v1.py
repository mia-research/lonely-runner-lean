"""Branch B: L(m) is blocked exactly at the colliders (8 | s), where L(m) = 0 mod b.
So the walk needed at a collider b is exactly L(b) steps, landing on the lower edge.
RULE to test:  q = L(m) + L(b*)  where b* is the collider.  Does it clear the profile?"""
from math import gcd, lcm
from functools import reduce
import random
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def clear(q,b): return L(b) <= q % b <= U(b)
# 1. exact law for when L(m) clears b
bad=0; tot=0
for m in range(2,2000):
    q=L(m)
    for b in range(2,m+1):
        if m%b: continue
        v=(m//b)%8; tot+=1
        want = (v!=0) and (-((-(v*b-1))//8) <= (7*b-1)//8)
        if clear(q,b)!=want: bad+=1
print(f"(1) L(m) clears b  <=>  v != 0 and ceil((v*b-1)/8) <= floor((7b-1)/8),  v = (m/b) mod 8")
print(f"    over {tot} pairs: {'HOLDS' if bad==0 else f'FAILS {bad}'}")
# 2. the collider step
random.seed(11)
hit=0; n=0; worst=[]
for _ in range(60000):
    m=random.choice([48,72,96,120,144,192,240,288,360,480,720,840,960,1440])
    divs=[d for d in range(2,m+1) if m%d==0]
    if len(divs)<5: continue
    bs=sorted(random.sample(divs,5))
    cols=[b for b in bs if (m//b)%8==0]
    if len(cols)!=1: continue                       # exactly one collider
    n+=1
    q=L(m)+L(cols[0])
    if all(clear(q,b) for b in bs): hit+=1
    elif len(worst)<6: worst.append((m,bs,cols[0],q))
print(f"\n(2) exactly one collider, rule q = L(m) + L(b*):")
print(f"    clears the whole profile in {hit}/{n} = {100*hit/n:.1f}%")
for w in worst: print(f"       miss: m={w[0]} bs={w[1]} collider={w[2]} q={w[3]}")
# 3. and how far does the walk actually go from L(m) in Branch B?
import statistics as st
d=[]
for _ in range(40000):
    m=random.choice([48,72,96,120,144,192,240,288,360,480,720,840])
    divs=[d2 for d2 in range(2,m+1) if m%d2==0]
    if len(divs)<5: continue
    bs=sorted(random.sample(divs,5))
    if not any((m//b)%8==0 for b in bs): continue
    M=reduce(lcm,bs)
    w=next((x for x in range(L(m), L(m)+M) if all(clear(x,b) for b in bs)), None)
    if w is not None: d.append(w-L(m))
print(f"\n(3) Branch B walk from L(m): median {st.median(d):.0f}  mean {st.mean(d):.1f}  max {max(d)}")
print(f"    equals max L(collider) exactly: measured separately below")
