r"""
ok_adversarial_v1 -- try to BREAK the apparent "speed floor ==> |G| bounded below" trend.

ok_finite_red_v2 found min |G| rising with the speed floor B: 0.0064, 0.0064, 0.0342,
0.0636, 0.0873, 0.0934 for B = 1,2,6,12,25,50.  But B >= 6 was RANDOMLY SAMPLED, and a
random 7-set from [B,TOP] will not be a near-dilate of the extremal tuple.

u and |G| are scale-invariant, so lambda*E has the same |G| -- but gcd(lambda E) = lambda,
which the problem forbids.  The adversarial family is therefore a dilate with ONE speed
perturbed just enough to restore gcd 1: min speed ~ 2*lambda, arbitrarily large, while the
arithmetic stays essentially that of the extremal tuple.

If |G| stays near 93/14560 along that family, the speed floor buys nothing and no finite
reduction of that shape exists.
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
print(f"base E = {BASE}   |G| = {g0} = {float(g0):.8f}   min speed {min(BASE)}")
print(f"\nadversarial family: lambda*BASE with one coordinate +1 to restore gcd 1\n")
print(f"{'lam':>4} {'perturbed tuple':38} {'min':>5} {'gcd':>4} {'|G|':>22} {'~':>11} {'vs base':>9}")
for lam in (2,3,5,7,11,15,21,30):
    for idx in range(7):
        E=[lam*e for e in BASE]
        E[idx]+=1
        E=tuple(sorted(E))
        if len(set(E))<7: continue
        if reduce(gcd,E)!=1: continue
        if not any(e%8==0 for e in E): continue      # keep it in Case 2
        g=G_measure(list(E))
        print(f"{lam:>4} {str(E):38} {min(E):>5} {reduce(gcd,E):>4} {str(g):>22} "
              f"{float(g):11.8f} {float(g/g0):9.2f}x")
        break
print(f"\nreference: (3/4)^7 = {float(F(3,4)**7):.8f} (independence);  base = {float(g0):.8f}")
