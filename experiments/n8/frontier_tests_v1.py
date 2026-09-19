"""(1) Does the gap rule preclude blockade?  (2) Is the blocking fraction exactly 1/4?
(3) The two frontier tests as described: mixed Branch B, and rational (no unit speed)."""
from math import gcd, lcm
from functools import reduce
import random
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def blocks(si,A,sk):
    M=8*sk; r=(si*A)%M; return min(r,M-r)<sk

print("(1) GapRule: gap between bad zones is N/(s*s'), N integer. N>=1 gives a gap >= 1/(s*s');")
print("    N<=0 means the zones OVERLAP -- no gap. Does blockade force N<=0?")
ds=[2,3,4,5,6,7,16]
for e in (3,4,5):
    neg=0; tot=0
    for si in ds:
        for sk in ds:
            if si>=sk: continue
            for q in range(0,6):
                for qp in range(0,6):
                    N = si*(8*qp+1) - sk*(8*q+1); tot+=1
                    if N<=0: neg+=1
    print(f"    flank e={e}: of {tot} zone pairs sampled, {neg} have N<=0 (overlap, no gap)")
print("    => the gap rule gives a LOWER BOUND on gaps that exist; it does not make them exist.")
print()
print("(2) is each disparity blocking exactly 1/4 of the residue ring?")
rows=[]
for e in range(2,17):
    for d in range(1,e+1):
        q=e//gcd(d,e)
        c=sum(1 for k in range(q) if blocks(d//(e//q), 8*k+1, q))
        rows.append((d,e,q,c,c/q))
fr=sorted(set(round(r[4],4) for r in rows))
print(f"    observed blocking fractions c/q: {fr}")
print(f"    exactly 1/4 in {sum(1 for r in rows if abs(r[4]-0.25)<1e-9)}/{len(rows)} cases")
print()
print("(3) frontier tests")
def clear_count(ss):
    """candidates (8q+1)/s_k over all readings s_k and q < s_k; count those clear"""
    n=0
    for sk in ss:
        for q in range(sk):
            A=8*q+1
            if all(not blocks(si,A,sk) for si in ss if si!=sk): n+=1
    return n
random.seed(5)
for name,gen,N in (
   ("Branch B mixed (integer, some 8|s, mixed scales)",
    lambda: sorted(set([1]+[random.choice([2,3,4,5,6,7])*random.choice([1,1,8])
                           for _ in range(6)]))[:7], 4000),
   ("rational: no unit speed (s_1 > 1)",
    lambda: sorted(set(random.sample(range(2,40),7))), 5000)):
    fails=0; mins=[]; n=0
    for _ in range(N*3):
        ss=gen()
        if len(ss)<7: continue
        if "Branch B" in name and not any(s%8==0 for s in ss): continue
        if "no unit" in name and 1 in ss: continue
        n+=1
        c=clear_count(ss)
        mins.append(c)
        if c==0: fails+=1
        if n>=N: break
    print(f"   {name}")
    print(f"      profiles {n}: failures {fails};  min clear candidates {min(mins)};  "
          f"median {sorted(mins)[len(mins)//2]}")
