r"""
ok_lowG_structure_v1 -- what do the HARDEST tuples look like?

|G| is fragile (moving one speed by 1 raises it 3-4.5x), so the low-|G| set should be thin
and arithmetically special.  This lists the smallest-|G| Case-2 tuples and reports their
additive structure: 3-term relations e_i + e_j = e_k, ratio-2 pairs, and how close the tuple
is to a dilated arithmetic progression -- the extremum (2,6,7,8,10,13,14) contains
2*{1,3,4,5,7} = 2*({1..7} \ {2,6}), and the Case-1 tight instance is the full AP {1..7}.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd

def arcs(e): return [(F(8*j+1,8*e), F(8*j+7,8*e)) for j in range(e)]
def inter(A,B):
    out=[]; i=j=0
    while i<len(A) and j<len(B):
        lo=max(A[i][0],B[j][0]); hi=min(A[i][1],B[j][1])
        if lo<hi: out.append((lo,hi))
        if A[i][1]<B[j][1]: i+=1
        else: j+=1
    return out
def G_measure(E):
    cur=arcs(E[0])
    for e in E[1:]:
        cur=inter(cur,arcs(e))
        if not cur: return F(0)
    return sum((b-a for a,b in cur), F(0))

def structure(E):
    S=set(E)
    add=[(a,b) for a in E for b in E if a<b and a+b in S]
    r2=[(a,2*a) for a in E if 2*a in S]
    # largest subset that is an AP after dividing by its gcd
    best=0; bestd=None
    for d in range(1,max(E)+1):
        for s in E:
            k=0
            while s+k*d in S: k+=1
            if k>best: best=k; bestd=(s,d)
    return add,r2,best,bestd

rows=[]
for E in combinations(range(1,25),7):
    if reduce(gcd,E)!=1: continue
    if not any(e%8==0 for e in E): continue
    rows.append((G_measure(list(E)),E))
rows.sort(key=lambda r:r[0])
print(f"{len(rows)} Case-2 tuples in [1..24].  The 12 with smallest |G|:\n")
print(f"{'E':32} {'|G|':>10} {'#(a+b=c)':>9} {'ratio-2 pairs':>26} {'longest AP':>11}")
for g,E in rows[:12]:
    add,r2,best,bestd=structure(E)
    print(f"{str(E):32} {float(g):10.6f} {len(add):>9} {str(r2):>26} {best:>4} (s={bestd[0]},d={bestd[1]})")
print("\nfor contrast, 6 random-ish Case-2 tuples from the MIDDLE of the |G| ordering:")
mid=len(rows)//2
for g,E in rows[mid:mid+6]:
    add,r2,best,bestd=structure(E)
    print(f"{str(E):32} {float(g):10.6f} {len(add):>9} {str(r2):>26} {best:>4} (s={bestd[0]},d={bestd[1]})")
import statistics
lo=[len(structure(E)[0]) for _,E in rows[:200]]
hi=[len(structure(E)[0]) for _,E in rows[-200:]]
print(f"\nmean #(a+b=c) relations: bottom-200 by |G| = {statistics.mean(lo):.2f}, "
      f"top-200 = {statistics.mean(hi):.2f}")
lo2=[structure(E)[2] for _,E in rows[:200]]; hi2=[structure(E)[2] for _,E in rows[-200:]]
print(f"mean longest AP length : bottom-200 = {statistics.mean(lo2):.2f}, "
      f"top-200 = {statistics.mean(hi2):.2f}")
