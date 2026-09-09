r"""
ok_relthresh_v1 -- is "few additive relations ==> |G| bounded below" a usable dichotomy?

Low-|G| tuples carry many 3-term relations e_i + e_j = e_k (mean 4.76 in the bottom 200 by
|G|, 0.77 in the top 200).  If min |G| rises sharply as the relation count falls, the proof
splits:  (i) FEW relations -> a decorrelation / first-moment bound;  (ii) MANY relations ->
a structured, finite classification.

Reported: min |G| by relation count, over all Case-2 tuples in [1..24].
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd
from collections import defaultdict

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
def nrel(E):
    S=set(E); return sum(1 for a in E for b in E if a<b and a+b in S)

buck=defaultdict(lambda: [None,None,0])   # min|G|, argmin, count
for E in combinations(range(1,25),7):
    if reduce(gcd,E)!=1: continue
    if not any(e%8==0 for e in E): continue
    k=nrel(E); g=G_measure(list(E))
    b=buck[k]; b[2]+=1
    if b[0] is None or g<b[0]: b[0]=g; b[1]=E
print(f"{'#relations':>11} {'count':>8} {'min |G|':>12} {'~':>10}  argmin")
for k in sorted(buck):
    g,E,c=buck[k]
    print(f"{k:>11} {c:>8} {str(g):>12} {float(g):10.6f}  {E}")
print(f"\nglobal target |G| >= 93/14560 = {float(F(93,14560)):.6f}")
z=buck.get(0)
if z: print(f"tuples with ZERO additive relations: {z[2]}, min |G| = {float(z[0]):.6f} "
            f"= {float(z[0]/F(93,14560)):.1f}x the global minimum")
