"""Step 2 of the proposed closure: does the order-6 clear window contain >= 2 consecutive
candidate grid points once m >= 12?
The margin 1/6 is a circle-DISTANCE, not a length in scale space. Measure the actual length of
the clear set (at the 1/8 threshold) around an order-6 witness, and count integers in it."""
from math import gcd, lcm
from functools import reduce
from fractions import Fraction as F
import random, statistics as st
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def clears(bs,q): return all(L(b) <= q % b <= U(b) for b in bs)
def band(b,q): r=q%b; return b-3 <= 6*r <= 5*b+3
random.seed(31)
print("For moduli bs, the clear set in q is {q : q mod b in [L(b),U(b)] for all b}.")
print("Longest run of CONSECUTIVE integers in it, against the claim '>= 2 once m >= 12':")
rows=[]
for _ in range(60000):
    m=random.choice([12,24,48,72,96,120,144,240,360,720,840,2520])
    divs=[d for d in range(1,m+1) if m%d==0]
    if len(divs)<7: continue
    ss=sorted(set([1,m]+random.sample(divs,5)))
    if len(ss)!=7: continue
    bs=sorted(set(m//si for si in ss if si!=m and m//si>1))
    if not bs: continue
    M=reduce(lcm,bs)
    if M>40000: continue
    best=0;cur=0
    for q in range(M):
        if clears(bs,q): cur+=1; best=max(best,cur)
        else: cur=0
    rows.append((m,min(bs),best))
    if len(rows)>=3000: break
print(f"   profiles {len(rows)}")
for lo,hi,lab in ((2,2,"b_min = 2"),(3,3,"b_min = 3"),(4,9,"b_min 4..9"),(10,10**9,"b_min >= 10")):
    sel=[r for r in rows if lo<=r[1]<=hi]
    if not sel: continue
    runs=[r[2] for r in sel]
    print(f"   {lab:12s} n={len(sel):5d}  longest run: median {st.median(runs):.0f}  "
          f"max {max(runs)}   >=2 consecutive in {100*sum(1 for x in runs if x>=2)/len(sel):5.1f}%")
print()
print("predicted window length in q-units is b_min/12 (from delta/b <= 1/6 - 1/8 = 1/24):")
for b in (2,3,8,9,12,24,48):
    print(f"   b_min = {b:2d}  ->  length {b}/12 = {b/12:.3f}   two consecutive integers need >= 2, "
          f"i.e. b_min >= 24: {'yes' if b>=24 else 'NO'}")
