r"""
ok_bonf_v1 -- Bonferroni attack on  int X >= 93/1820.

At each x the blocked set is a UNION of 7 subsets of Z/8, bad_e(x).  Write
    S_k(x) = sum over k-subsets F of E of |intersection of bad_e(x), e in F|.
Bonferroni:  |union| <= S_1 - S_2 + S_3,   |union| >= S_1 - S_2 + S_3 - S_4 + S_5, ...
so with X = 8 - |union|,  EVERY ODD TRUNCATION IS A VALID LOWER BOUND ON X:

    X  >=  8 - S_1 + S_2 - S_3                     (order 3)
    X  >=  8 - S_1 + S_2 - S_3 + S_4 - S_5         (order 5)
    X  =   8 - S_1 + S_2 - S_3 + S_4 - S_5 + S_6 - S_7   (exact, order 7)

Integrating preserves the inequalities.  Under independence int S_k = 8*C(7,k)/4^k, giving
int X ~ 8(3/4)^7 = 1.0679; the truth at the extremal tuple is 0.0511, so the question is
what the EXACT S_k do.  All terms below are exact rationals.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import reduce
from math import gcd, comb
import sys

def bad(e,t): return frozenset(r for r in range(8) if ((e%8)*r+t)%8 in (0,7))
def cells(E):
    pts={F(0),F(1)}
    for e in E:
        for j in range(1,e+1):
            q=F(j,e)
            if 0<q<1: pts.add(q)
    p=sorted(pts); return list(zip(p,p[1:]))
def fl(e,a): v=e*a; return v.numerator//v.denominator

def S_profile(E):
    """exact int S_k for k = 1..7, and exact int X"""
    n=len(E); S=[F(0)]*(n+1); intX=F(0)
    for a,b in cells(E):
        w=b-a
        B=[bad(e,fl(e,a)) for e in E]
        for k in range(1,n+1):
            tot=0
            for F_ in combinations(range(n),k):
                s=B[F_[0]]
                for i in F_[1:]:
                    s=s&B[i]
                    if not s: break
                tot+=len(s)
            S[k]+=tot*w
        cov=set()
        for s in B: cov|=s
        intX+=(8-len(cov))*w
    return S,intX

def bonf(S,order):
    v=F(8)
    for k in range(1,order+1):
        v += (-1)**k * S[k]
    return v

M=(2,6,7,8,10,13,14)
S,intX=S_profile(list(M))
print(f"extremal tuple E = {M}")
print(f"  exact int X = {intX} = {float(intX):.6f}   (target constant 93/1820)")
print(f"\n  {'k':>2} {'int S_k exact':>18} {'~':>10} {'independence 8*C(7,k)/4^k':>26}")
for k in range(1,8):
    ind=F(8*comb(7,k),4**k)
    print(f"  {k:>2} {str(S[k]):>18} {float(S[k]):10.5f} {float(ind):26.5f}")
print(f"\n  Bonferroni lower bounds on int X (odd orders are valid lower bounds):")
for o in (1,3,5,7):
    v=bonf(S,o)
    tag = "= exact" if o==7 else ("OK, positive" if v>0 else "negative -- useless")
    print(f"    order {o}: {str(v):>20} = {float(v):10.6f}   {tag}")
print(f"\n  even orders (valid UPPER bounds on int X):")
for o in (2,4,6):
    print(f"    order {o}: {float(bonf(S,o)):10.6f}")
