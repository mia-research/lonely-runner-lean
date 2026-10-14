# PREREG: docs/n8/PREREG_WITNESS_PERTURBATION_v1.md (axis A7: move the flank, not the constraints)
# How often does the LARGEST flank fail to host a witness? Exhaustive, exact integer arithmetic.
from itertools import combinations
from math import gcd
import sys, collections
def supports(ds,e):
    M=8*e; lo=e; hi=7*e
    r=[d % M for d in ds]; st=[(8*d)%M for d in ds]
    for _ in range(e):
        if all(lo<=x<=hi for x in r): return True
        for i in range(7): r[i]=(r[i]+st[i])%M
    return False
H=int(sys.argv[1]) if len(sys.argv)>1 else 30
n=0; fail=[]; rank_needed=collections.Counter()
for c in combinations(range(1,H+1),7):
    g=0
    for x in c: g=gcd(g,x)
    if g!=1: continue
    n+=1
    if not supports(c,c[-1]):
        srt=sorted(c,reverse=True)
        r=next((i+1 for i,e in enumerate(srt) if supports(c,e)), None)
        rank_needed[r]+=1
        if len(fail)<25: fail.append((c,r))
print(f"exhaustive primitive 7-subsets of [1,{H}]: {n}")
print(f"largest flank FAILS to host a witness: {len(fail) if len(fail)<25 else sum(rank_needed.values())} "
      f"({100*sum(rank_needed.values())/n:.4f}%)")
print(f"best rank needed when it fails: {dict(sorted(rank_needed.items()))}")
for c,r in fail: print(f"   {c}  needs rank {r}")
