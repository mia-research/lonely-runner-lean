#!/usr/bin/env python3
"""Does the residue class mod 8 DETERMINE the grid certificate?
If yes, 'account for the gaps' is a finite problem. If no, measure the residue.
Group every Case-2 tuple in [1..18] by its residue multiset mod 8 and test homogeneity."""
from fractions import Fraction as F
from itertools import combinations, product
from functools import reduce
from math import gcd
from collections import defaultdict

def LU(E,a): return (max(F(1-(e*a)%8,8*e) for e in E), min(F(7-(e*a)%8,8*e) for e in E))
def cert(E):  return any(LU(E,a)[0]<=LU(E,a)[1] for a in (1,3,5,7))
def certK(E,K=1):
    for a in (1,3,5,7):
        ivs=[[(F(1-(e*a)%8,8*e)+F(k,e), F(7-(e*a)%8,8*e)+F(k,e)) for k in range(-K,K+1)] for e in E]
        for c in product(*ivs):
            if max(x for x,_ in c) <= min(y for _,y in c): return True
    return False

groups=defaultdict(list)
for E in combinations(range(1,19),7):
    if reduce(gcd,E)!=1 or all(e%8 for e in E): continue
    groups[tuple(sorted(e%8 for e in E))].append(E)
print(f"Case-2 tuples in [1..18]: {sum(len(v) for v in groups.values())}")
print(f"distinct residue multisets mod 8: {len(groups)}")

for lab,f in (("principal certificate",cert),("K=1 certificate",certK)):
    allyes=allno=mixed=0; ex=None
    for R,Es in groups.items():
        vals={f(E) for E in Es}
        if vals=={True}: allyes+=1
        elif vals=={False}: allno+=1
        else:
            mixed+=1
            if ex is None:
                y=next(E for E in Es if f(E)); n=next(E for E in Es if not f(E))
                ex=(R,y,n)
    tot=len(groups)
    print(f"\n{lab}: of {tot} residue classes")
    print(f"   homogeneous YES {allyes} ({100*allyes/tot:.1f}%)   homogeneous NO {allno} ({100*allno/tot:.1f}%)"
          f"   MIXED {mixed} ({100*mixed/tot:.1f}%)")
    if ex:
        R,y,n=ex
        print(f"   e.g. residues {R}: fires for {y}, fails for {n}  <- same class, different answer")

print("\nHow much of the tuple population lives in MIXED classes?")
for lab,f in (("principal",cert),("K=1",certK)):
    mx=sum(len(Es) for R,Es in groups.items() if len({f(E) for E in Es})>1)
    tot=sum(len(v) for v in groups.values())
    print(f"   {lab:>10}: {mx}/{tot} = {100*mx/tot:.2f}% of tuples are in a class that is not decided by residues")
