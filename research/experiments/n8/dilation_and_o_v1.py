r"""
Two things.

(1) DILATION THEOREM.  |S(E_non)| is invariant under E_non -> lambda*E_non.
    Proof: the safe condition at x is  "exists r with (e*r + floor(e*x)) mod 8 not in
    {0,7} for all e".  Replacing e by lambda*e gives floor(lambda*e*x) = floor(e*(lambda x)),
    so the state at x for lambda*E equals the state at lambda*x for E.  Moreover the
    state at w+1 equals the state at w with r shifted by 1, because
        e*(r+1) + floor(e*w) = e*r + (floor(e*w) + e) = e*r + floor(e*(w+1)),
    so SAFETY is invariant under w -> w+1.  Hence S(lambda*E) = (1/lambda)(S(E) + Z),
    a lambda-fold contraction of a period-1 set, of the SAME measure.  []
    Checked numerically below.

(2) The quantity that decides the remaining gap.  For the four unit runners put
        O = {x : they block all four ODD residues},   o = |O|
        U = {x : they block all of Z/8},              u = |U| <= o.
    The fibre criterion closes a unit 4-tuple once o (resp. o+u) is small enough; the
    only tuples observed to fail are the dilation orbit of (1,3,5,7).  So the sharp
    question is: for which unit 4-tuples is o large?
    By the PAIR RULE a unit runner of residue rho blocks the odd residue -tau*rho,
    tau = the odd member of {t, t+1} = 2*floor(t/2)+1.  So O is exactly the set where
    rho -> tau_rho * rho is a bijection of (Z/8)* -- 24 of the 4^4 = 256 tau-vectors.
"""
from fractions import Fraction as F
from math import gcd
import itertools, sys

def cells(S):
    pts={F(0),F(1)}
    for e in S:
        for j in range(1,e+1):
            q=F(j,e)
            if 0<q<1: pts.add(q)
    p=sorted(pts); return list(zip(p,p[1:]))
def fl(e,a): v=e*a; return v.numerator//v.denominator          # ENTRY, never a midpoint
def bad(e,t): return frozenset(r for r in range(8) if (e*r+t)%8 in (0,7))
FULL=frozenset(range(8)); ODD=frozenset({1,3,5,7})

def safe_meas(S):
    tot=F(0)
    for a,b in cells(S):
        cov=set()
        for e in S: cov|=bad(e,fl(e,a))
        if cov!=FULL: tot+=b-a
    return tot
def o_u(U4):
    o=F(0); u=F(0)
    for a,b in cells(U4):
        cov=set()
        for e in U4: cov|=bad(e,fl(e,a))
        if ODD<=cov: o+=b-a
        if cov==FULL: u+=b-a
    return o,u

print("(1) Dilation Theorem, checked: |S(lam*E_non)| vs |S(E_non)|")
base=[1,3,5,7,4]
for lam in (1,3,5,7,9,11):
    print(f"    lam={lam:>3}: |S| = {safe_meas([lam*e for e in base])}")
print(f"    also on a non-exceptional base {(1,3,5,7,2)}:")
for lam in (1,3,5):
    print(f"    lam={lam:>3}: |S| = {safe_meas([lam*e for e in (1,3,5,7,2)])}")

print("\n(2) o and u for unit 4-tuples (e_1,e_3,e_5,e_7), e_rho = rho mod 8")
print(f"{'tuple':>22} {'gcd':>4} {'o':>12} {'o~':>8} {'u':>10} {'u~':>8} {'o+u<=1?':>9}")
rows=[]
for qs in itertools.product(range(0,4),repeat=4):
    U4=tuple(8*q+r for q,r in zip(qs,(1,3,5,7)))
    if len(set(U4))!=4: continue
    o,u=o_u(list(U4)); g=0
    for e in U4: g=gcd(g,e)
    rows.append((o,u,U4,g))
rows.sort(reverse=True)
for o,u,U4,g in rows[:14]:
    print(f"{str(U4):>22} {g:>4} {str(o):>12} {float(o):>8.4f} {str(u):>10} {float(u):>8.4f} {str(o+u<=1):>9}")
big=[r for r in rows if r[0]>F(1,2)]
print(f"\n    tuples with o > 1/2 : {len(big)} of {len(rows)}")
for o,u,U4,g in big: print(f"       {U4}  gcd={g}  o={o}  u={u}   primitive={g==1}")
