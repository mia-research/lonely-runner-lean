from itertools import combinations
from math import gcd
from functools import reduce
import collections
def nopen(ds,e):
    M=8*e; r=[d%M for d in ds]; st=[(8*d)%M for d in ds]; c=0
    for _ in range(e):
        if all(e<=x<=7*e for x in r): c+=1
        for i in range(7): r[i]=(r[i]+st[i])%M
    return c
def supports(ds,e): return nopen(ds,e)>0
def mincd(ds,e): return min(e//gcd(d,e) for d in ds if d!=e)

print("CLAIM: for d < e,  c_d = e/gcd(d,e) = m  <=>  d is j*e/m with gcd(j,m)=1.")
print("In particular  min c_d = 2  <=>  e/2 is itself a disparity.\n")
bad=0
for e in range(2,60):
    for d in range(1,e):
        m=e//gcd(d,e)
        if (m==2) != (2*d==e): bad+=1
print(f"  checked all (d,e) with d<e<60: mismatches for the m=2 case: {bad}")

H=30
print(f"\nSELECTOR TEST on exhaustive primitive 7-subsets of [1,{H}]")
print("Candidate: choose the flank that MAXIMISES min_d c_d (least harmonised), tie-break largest.\n")
res=collections.Counter(); n=0
fails_max=0; fails_sel=0; ex=[]
for c in combinations(range(1,H+1),7):
    if reduce(gcd,c)!=1: continue
    n+=1
    if not supports(c,c[-1]): fails_max+=1
    sel=max(c, key=lambda e:(mincd(c,e), e))
    if not supports(c,sel):
        fails_sel+=1
        if len(ex)<10: ex.append((c,sel,mincd(c,sel)))
print(f"  sets: {n}")
print(f"  flank = d_max                : {fails_max:5d} failures  ({100*fails_max/n:.4f}%)")
print(f"  flank = argmax min c_d       : {fails_sel:5d} failures  ({100*fails_sel/n:.4f}%)")
if fails_max: print(f"  improvement factor           : {fails_max/max(fails_sel,1):.1f}x")
for t in ex: print(f"     still fails: {t[0]}  selected flank {t[1]} (min c_d = {t[2]})")

print("\n  and the two combined (try argmax-min-c_d, else d_max, else next largest):")
both=0
for c in combinations(range(1,H+1),7):
    if reduce(gcd,c)!=1: continue
    sel=max(c, key=lambda e:(mincd(c,e), e))
    if supports(c,sel) or supports(c,c[-1]): continue
    both+=1
print(f"  neither works: {both} ({100*both/n:.4f}%)")
