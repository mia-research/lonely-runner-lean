"""
End-to-end verification of the claimed theorem for the Unit-Complete leaf at n=8,
representative speeds.  Exact integer/rational arithmetic; no floating point in any
decision.

E = {1,3,5,7,rho0} u {8*m1, 8*m2},  rho0 in {2,4,6}, m1 != m2 positive.
Then R_non = {1,3,5,7,rho0}; the two dropped classes are {2,4,6}\{rho0}, both
non-units, so the tuple is Unit-Complete.  gcd(E) = 1 since 1 in E.

Claim chain:
 (i)  bridge: k = b + r*L is a loneliness witness iff for every e in E,
      (e*r + floor(e*b/L)) mod 8 in {1,...,6}.
 (ii) for e = 8m this is independent of r and says exactly ||m*b/L|| >= 1/8.
 (iii) all breakpoints are at integer b (every e in E divides L), so measures are
      exact integer counts.
 (iv) |S(2)| = 22/35, |S(4)| = 5/14, |S(6)| = 6/7; |B_m| = 1/4 exactly.
      rho0 = 2,6: |S| > 1/2 = 2*|B_m|, union bound gives a good b.
      rho0 = 4: |S| = 5/14 < 1/2, needs Lemma D (B_m1 u B_m2 misses [1/4,3/7)).
"""
from fractions import Fraction as F
from math import lcm, gcd
import itertools, sys

def ok(e,r,t): return (e*r+t)%8 in range(1,7)

def check_tuple(E):
    L=lcm(*E); good=[]
    for b in range(L):
        T={e:(e*b)//L for e in E}
        for r in range(8):
            if all(ok(e,r,T[e]) for e in E):
                good.append((b,r)); break
    return L,good

def verify_witness(E,L,b,r):
    """k = b + rL must satisfy ||e k/(8L)|| >= 1/8 for all e."""
    k=b+r*L; N=8*L
    for e in E:
        v=(e*k)%N
        if not (L<=v<=7*L): return False,e
    return True,None

bad_cases=[]; checked=0
for rho0 in (2,4,6):
    for m1,m2 in itertools.combinations(range(1,13),2):
        E=tuple(sorted({1,3,5,7,rho0,8*m1,8*m2}))
        if len(E)!=7: continue
        g=0
        for e in E: g=gcd(g,e)
        assert g==1
        L,good=check_tuple(E)
        checked+=1
        if not good: bad_cases.append(E); continue
        b,r=good[0]
        okk,bade=verify_witness(E,L,b,r)
        if not okk: bad_cases.append((E,'witness fails',bade))
print(f"tuples checked: {checked}")
print(f"tuples with NO good (b,r): {len([c for c in bad_cases if isinstance(c,tuple) and len(c)==7])}")
print(f"tuples where the produced witness fails: {len([c for c in bad_cases if not (isinstance(c,tuple) and len(c)==7)])}")
if bad_cases: print("  FAILURES:", bad_cases[:5])
else: print("  -> every tuple has a good (b,r), and k = b + rL is a genuine witness.")

# Lemma D case boundaries, checked exactly
def B(m):
    out=[]
    for j in range(0,m+1):
        lo,hi=max(F(j,m)-F(1,8*m),F(0)),min(F(j,m)+F(1,8*m),F(1))
        if lo<hi: out.append((lo,hi))
    return out
I=(F(1,4),F(3,7))
def inter(win,ivs):
    lo,hi=win; tot=F(0); parts=[]
    for a,b in ivs:
        a2,b2=max(a,lo),min(b,hi)
        if a2<b2: parts.append((a2,b2)); tot+=b2-a2
    return tot,parts
print("\nLemma D, the small-m table (B_m intersected with I = [1/4,3/7), |I| = 5/28):")
for m in range(1,8):
    t,p=inter(I,B(m))
    print(f"   m={m}: |B_m n I| = {t} = {float(t):.4f}   parts {[(str(a),str(b)) for a,b in p]}")
print(f"   period 1/m <= |I| = 5/28 iff m >= 28/5 = 5.6, i.e. m >= 6"
      f"  -> I then contains a full gap of B_m, of length 3/(4m)")
