from itertools import combinations
from math import gcd
from functools import reduce
import collections
def supports(ds,e):
    M=8*e; r=[d%M for d in ds]; st=[(8*d)%M for d in ds]
    for _ in range(e):
        if all(e<=x<=7*e for x in r): return True
        for i in range(7): r[i]=(r[i]+st[i])%M
    return False
H=30
fail_by_dmax=collections.Counter(); all_by_dmax=collections.Counter()
fail_has1=0; all_has1=0; fails=[]
for c in combinations(range(1,H+1),7):
    if reduce(gcd,c)!=1: continue
    e=c[-1]; all_by_dmax[e]+=1; all_has1 += (c[0]==1)
    if not supports(c,e):
        fail_by_dmax[e]+=1; fail_has1 += (c[0]==1); fails.append(c)
n=sum(all_by_dmax.values()); F=len(fails)
print(f"primitive 7-subsets of [1,{H}]: {n};  d_max flank fails: {F} ({100*F/n:.4f}%)\n")
print(f"{'d_max':>6} {'sets':>9} {'failures':>9} {'rate %':>9}")
for e in sorted(all_by_dmax):
    f=fail_by_dmax.get(e,0)
    if f or e<=16:
        print(f"{e:>6} {all_by_dmax[e]:>9} {f:>9} {100*f/all_by_dmax[e]:>9.4f}")
print(f"\nd_min = 1 present:  in all sets {100*all_has1/n:.1f}%   in failures {100*fail_has1/F:.1f}%")
print(f"\nthe span d_max/d_min in failures:")
sp=collections.Counter()
for c in fails: sp[round(c[-1]/c[0])]+=1
print("  ", dict(sorted(sp.items())[:14]))
print("\nexactly how large is d_max in failures?")
q=sorted(c[-1] for c in fails)
print(f"  min {q[0]}  median {q[len(q)//2]}  p90 {q[int(.9*len(q))]}  max {q[-1]}  (range cap {H})")
print("\nControl: is it just 'd_max small'? failure rate at d_max <= 16 vs > 16:")
lo=sum(v for k,v in all_by_dmax.items() if k<=16); lof=sum(v for k,v in fail_by_dmax.items() if k<=16)
hi=sum(v for k,v in all_by_dmax.items() if k>16); hif=sum(v for k,v in fail_by_dmax.items() if k>16)
print(f"  d_max <= 16: {lof}/{lo} = {100*lof/lo:.4f}%")
print(f"  d_max  > 16: {hif}/{hi} = {100*hif/hi:.4f}%")
