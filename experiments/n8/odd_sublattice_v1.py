"""Repair: force q odd from the start. Substitute q = 2u+1 and ask about the u-problem.
At odd b, 2 is invertible so u ranges over all residues and the window keeps its width.
At even b, 2u+1 is always odd, so only the odd residues of b are reachable -- the effective
modulus halves. Does that make the obstruction go away, or move?"""
from math import gcd, lcm
from functools import reduce
import random, statistics as st
def L(b): return -((-(b-1))//8)
def U(b): return (7*b-1)//8
def clear(b,q): return L(b) <= q % b <= U(b)
print("effective u-window at each b, after q = 2u+1:")
for b in range(2,18):
    us=[u for u in range(b) if clear(b,2*u+1)]
    print(f"   b={b:2d}: clear q-residues {[r for r in range(b) if clear(b,r)]}"
          f"   -> clear u mod {b}: {us}  ({len(us)}/{b})")
print()
print("longest run of consecutive u with 2u+1 clear at every modulus:")
random.seed(31)
rows=[]
for _ in range(60000):
    m=random.choice([24,48,72,96,120,144,240,360,720,840,2520])
    divs=[d for d in range(1,m+1) if m%d==0]
    if len(divs)<7: continue
    ss=sorted(set([1,m]+random.sample(divs,5)))
    if len(ss)!=7: continue
    bs=sorted(set(m//si for si in ss if si!=m and m//si>1))
    if not bs or 2 not in bs: continue          # the hard case: b = 2 present
    M=reduce(lcm,bs)
    if M>40000: continue
    best=0;cur=0
    for u in range(M):
        if all(clear(b,2*u+1) for b in bs): cur+=1; best=max(best,cur)
        else: cur=0
    rows.append((min(b for b in bs if b>2) if any(b>2 for b in bs) else 2, best))
    if len(rows)>=1500: break
runs=[r[1] for r in rows]
print(f"   profiles with b=2 present: {len(rows)}")
print(f"      longest run in u: median {st.median(runs):.0f}  max {max(runs)}  "
      f">=2 consecutive: {100*sum(1 for x in runs if x>=2)/len(runs):.1f}%")
print(f"      runs of 0 (no witness on the odd sublattice): {sum(1 for x in runs if x==0)}")
