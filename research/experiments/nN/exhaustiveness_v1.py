"""Item 3, started: with each family's condition now exact, what survives ALL of them?

Conditions as proved, not as measured:
  DIV   ratWorks_one_iff        : exists q in [2,n] with no disparity divisible by q
  COP   coprime_rule_applies_iff: no disparity divisible by n  -- SUBSUMED by DIV at q = n
  SELF  flankWorks_of_multiples : some flank with all non-flank disparities multiples of n
  BAND  bandFits_forces_spread  : some flank e and (k,M) with the two integer inequalities
                                  (k = 0, flank = d_min is Theorem 4.8)
Counts, not shares.
"""
from itertools import combinations
import math
def DIV(ds, n):
    for q in range(2, n+1):
        if all(d % q for d in ds): return q
    return None
def SELF(ds, n):
    for e in ds:
        if all(d % n == 0 for d in ds if d != e): return e
    return None
def BAND(ds, n, KMAX=60, MMAX=60):
    for e in ds:
        rest = [d for d in ds if d != e]
        if not rest: return (e,0,0)
        lo, hi = min(rest), max(rest)
        for k in range(KMAX):
            T = n*k+1
            if (hi-lo)*T > e*(n-2): break          # the necessary spread bound
            for M in range(MMAX):
                if e*(n*M+1) <= lo*T and hi*T <= e*(n*M+n-1): return (e,k,M)
    return None
for n, HI in ((5,26),(6,20),(7,15),(8,13)):
    k=n-1; tot=0; d_=0; s_=0; b_=0; union=0; left=[]
    for c in combinations(range(1,HI+1),k):
        g=c[0]
        for x in c[1:]: g=math.gcd(g,x)
        if g!=1: continue
        tot+=1
        D,S,B = DIV(c,n), SELF(c,n), BAND(c,n)
        d_+= D is not None; s_+= S is not None; b_+= B is not None
        if D or S or B: union+=1
        else: left.append(c)
    print(f"n={n}  primitive {k}-sets in [1,{HI}]: {tot}")
    print(f"   DIV fires {d_}   SELF fires {s_}   BAND fires {b_}")
    print(f"   union {union}   SURVIVES ALL THREE: {len(left)}   {left[:5]}")
    print()
