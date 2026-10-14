"""At a candidate A/s_k in band 0, self_never_blocks frees s_k and unit_never_blocks frees s=1,
leaving at most 5 active blockers -- an ORDER-6 count, and order 6 is ours (margin 1/6 > 1/8).
Verify the count, and check that each choice of generating reading k gives an independent chance."""
from math import gcd
from functools import reduce
import random
def blocks(si,A,sk):
    M=8*sk; r=(si*A)%M; return min(r,M-r)<sk
random.seed(11)
bad=0; tot=0; maxb=0
for _ in range(60000):
    ss=sorted(set([1]+random.sample(range(2,60),6)))
    if len(ss)!=7: continue
    for sk in ss:
        for q in range(sk):
            A=8*q+1
            if not (sk <= A <= 7*sk): continue      # band 0
            act=[si for si in ss if blocks(si,A,sk)]
            tot+=1; maxb=max(maxb,len(act))
            if sk in act or 1 in act: bad+=1
print(f"candidates in band 0 checked: {tot}")
print(f"   s_k or the unit reading ever blocks: {bad}  {'(NEVER -- as proved)' if bad==0 else 'VIOLATION'}")
print(f"   maximum active blockers seen: {maxb}   (n-3 = 5 is the proved bound)")
print()
print("seven generating readings = seven independent order-6 problems; how many k work?")
import statistics as st
cnt=[]
for _ in range(4000):
    ss=sorted(set([1]+random.sample(range(2,40),6)))
    if len(ss)!=7: continue
    good=0
    for sk in ss:
        if any(sk <= 8*q+1 <= 7*sk and all(not blocks(si,8*q+1,sk) for si in ss)
               for q in range(sk)): good+=1
    cnt.append(good)
print(f"   generating readings admitting a clear candidate: min {min(cnt)}, "
      f"median {st.median(cnt):.0f}, max {max(cnt)} of 7")
print(f"   profiles with ZERO working k: {sum(1 for c in cnt if c==0)}")
