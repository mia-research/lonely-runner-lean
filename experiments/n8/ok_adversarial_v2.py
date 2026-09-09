r"""
ok_adversarial_v2 -- proper adversarial search.  v1 perturbed only the FIRST coordinate
(it broke out of the loop), so it tested one family, not the family.  Here: every position,
every offset in +-{1,2,3,4,5,6,7,8}, gcd 1, still Case 2, and report the MINIMUM |G| --
the best the adversary can do at each speed floor.
"""
from fractions import Fraction as F
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

BASE=(2,6,7,8,10,13,14)
g0=G_measure(list(BASE))
print(f"base {BASE}  |G| = {float(g0):.8f}\n")
print(f"{'lam':>4} {'minspeed':>9} {'best |G| adversary can reach':>30} {'~':>11} {'vs base':>9}  tuple")
for lam in (2,3,5,7,11,15,21,30,50):
    best=None
    for idx in range(7):
        for d in (1,-1,2,-2,3,-3,4,-4,5,-5,6,-6,7,-7,8,-8):
            E=[lam*e for e in BASE]; E[idx]+=d
            if E[idx]<1: continue
            E=tuple(sorted(E))
            if len(set(E))<7: continue
            if reduce(gcd,E)!=1: continue
            if not any(e%8==0 for e in E): continue
            g=G_measure(list(E))
            if best is None or g<best[0]: best=(g,E)
    if best is None: continue
    g,E=best
    print(f"{lam:>4} {min(E):>9} {str(g):>30} {float(g):11.8f} {float(g/g0):9.2f}x  {E}")
print(f"\nreference (3/4)^7 = {float(F(3,4)**7):.8f}")
print("If the best adversarial |G| stays well above the base, the extremum is FRAGILE:")
print("it needs exact arithmetic relations, which gcd 1 at large speeds cannot sustain.")
