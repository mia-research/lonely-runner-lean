"""
Pentagon de-risk: does the pentagon P kill the (1,2)/(1,-2) survivors, or do they
need Table-1 realizability instead?

P (from no_good_time_P, reduced by /w2=gq; g cancels) for the point (X,Y)=
({w3 t},{w0 t}) at a half-integer time ({w2 t}=1/2), given reduced speeds
p=v1·q, p2=v2·q, q, r=v4·q, s=v5·q  (so p<p2<q<r<s):
  h39:  X >= 1/6 - r(s-q)/(3 q s)
  h40:  Y >= 1/6 - p(s-q)/(3 q s)
  h41:  Y <= 1/3 + p2(s-q)/(3 q s)
  hxle: X <= 5/6
  h42a: 1/(3s) <= (5/6 - X)/r + (Y - 1/6)/p
  h42b: 1/(3s) <= (5/6 - X)/r + (1/3 - Y)/p2
If some half-integer time (S-point) satisfies all 6, no_good_time_P ⟹ False (killed).

S-point at l: X=frac(r(2l+1)/2q), Y=frac(p(2l+1)/2q)  (same coset as R-witnesses).

Question: for (1,2)-survivors (C∩R=∅, q>=18), and valid completions (p2,s), does a
pentagon witness ALWAYS exist (pentagon kills) or are there (p2,s) with NO witness
(⟹ Table-1 needed)?  Pentagon grows with s, so smallest s is hardest.
"""
from math import gcd
from fractions import Fraction as F

def frac(x): return x - (x.numerator // x.denominator)
def S(l, p, q, r):
    u = 2*l + 1
    return frac(F(r*u, 2*q)), frac(F(p*u, 2*q))
XLO, XHI, YLO, YHI = F(1,6), F(1,2), F(1,6), F(1,3)
def inR(X, Y): return XLO <= X <= XHI and YLO <= Y <= YHI
def cap_R_empty(p, q, r): return all(not inR(*S(l,p,q,r)) for l in range(q))

def in_G(i, j, p, q, r):
    return any((m*r) % q == i % q and (m*p) % q == j % q for m in range(q))
def is_pair_12(p, q, r):
    """is (1,2) box-minimal? quick: (1,2) in G-cone and minimal."""
    # (1,2) in G:
    if not in_G(1, 2, p, q, r): return False
    # minimal: no nonzero (k,l), |k|<=1,|l|<=2, not (±1,±2), in G
    for k in (-1,0,1):
        for l in range(-2,3):
            if (k,l)==(0,0) or (abs(k)==1 and abs(l)==2): continue
            if in_G(k,l,p,q,r): return False
    return True

def pent_witness(p, p2, q, r, s):
    """does some S-point satisfy all 6 pentagon conditions?"""
    e1 = F(r*(s-q), 3*q*s); e0 = F(p*(s-q), 3*q*s); e2 = F(p2*(s-q), 3*q*s)
    for l in range(q):
        X, Y = S(l, p, q, r)
        if not (X >= F(1,6)-e1): continue
        if not (Y >= F(1,6)-e0): continue
        if not (Y <= F(1,3)+e2): continue
        if not (X <= F(5,6)): continue
        lhs = F(1, 3*s)
        if lhs <= (F(5,6)-X)/r + (Y-F(1,6))/p and lhs <= (F(5,6)-X)/r + (F(1,3)-Y)/p2:
            return l
    return None

# collect (1,2) survivors
survs = []
for q in range(18, 46):
    for p in range(1, q):
        if 3*p >= q or gcd(p,q)!=1: continue
        for r in range(q+1, (3*q)//2+1):
            if 2*r >= 3*q: continue
            if is_pair_12(p,q,r) and cap_R_empty(p,q,r):
                survs.append((p,q,r))
print(f"(1,2) survivors (q<46): {len(survs)}")

# For each survivor, scan completions (p2,s): p<p2<q, r<s<=3q. Does a pentagon
# witness exist?  Report: tuples where SOME (p2,s) has NO witness (pentagon fails).
fail_any = []   # (p,q,r) with some valid (p2,s) lacking a witness
no_valid = 0
for (p,q,r) in survs:
    bad = []
    nvalid = 0
    for p2 in range(p+1, q):
        for s in range(r+1, 3*q+1):
            nvalid += 1
            if pent_witness(p, p2, q, r, s) is None:
                bad.append((p2, s))
    if nvalid == 0:
        no_valid += 1
    elif bad:
        fail_any.append((p, q, r, len(bad), nvalid, bad[:3]))

print(f"survivors with >=1 (p2,s) lacking a pentagon witness: {len(fail_any)} / {len(survs)}")
for t in fail_any[:25]:
    print(f"   p={t[0]} q={t[1]} r={t[2]}: {t[3]}/{t[4]} (p2,s) have NO witness; e.g. {t[5]}")
