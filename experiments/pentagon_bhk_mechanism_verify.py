"""
Verify BHK's ACTUAL Case 5.2.9 (1,-2)_S and 5.2.11 (1,2)_U mechanisms close all
q>=18, so the Lean formalization needs NO Diophantine tail. Corrections vs prior
de-risk: (i) p2 = w1/g = q-p is FIXED (hsum), not free; (ii) rigidity forced
(1,2): 2r-p=2q, p=2(r-q); (1,-2): 2r+p=3q; (iii) BHK uses horizontal length
(case a, spacing i/q=1/q) OR vertical length (case b, spacing |j|/q=2/q).
Completion free var: s = w4/g in (r, 3q].
"""
from math import gcd
from fractions import Fraction as F

def frac(x): return x - (x.numerator // x.denominator)
def Cpts(p, q, r):
    return [(frac(F(r*(2*l+1), 2*q)), frac(F(p*(2*l+1), 2*q))) for l in range(q)]

def in_P(X, Y, p, q, r, s):
    p2 = q - p                       # = w1/g, FIXED
    e1 = F(r*(s-q), 3*q*s); e0 = F(p*(s-q), 3*q*s); e2 = F(p2*(s-q), 3*q*s)
    return (X >= F(1,6)-e1 and Y >= F(1,6)-e0 and Y <= F(1,3)+e2 and X <= F(5,6)
            and F(1,3*s) <= (F(5,6)-X)/r + (Y-F(1,6))/p
            and F(1,3*s) <= (F(5,6)-X)/r + (F(1,3)-Y)/p2)

def in_G(i, j, p, q, r):
    return any((m*r) % q == i % q and (m*p) % q == j % q for m in range(q))
def is_pair(ii, jj, p, q, r):
    if not in_G(ii, jj, p, q, r): return False
    for k in range(-abs(ii), abs(ii)+1):
        for l in range(-abs(jj), abs(jj)+1):
            if (k,l)==(0,0) or (abs(k)==abs(ii) and abs(l)==abs(jj)): continue
            if in_G(k,l,p,q,r): return False
    return True

# ---- (1,-2): rigidity 2r+p=3q; vertical-1/6 segment -> C∩P != ∅ for q>=12 -----
print("=== (1,-2)_S : C∩P != ∅ via vertical-1/6 crossing (expect all q>=18 ok) ===")
fail = rig = tot = 0
for q in range(18, 81):
    for p in range(1, q):
        if 3*p >= q or gcd(p, q) != 1: continue
        if (3*q - p) % 2 != 0: continue
        r = (3*q - p)//2
        if not (q < r < F(3*q,2)) or 2*r >= 3*q: continue
        if not (is_pair(1, -2, p, q, r)): continue
        if 2*r + p != 3*q: rig += 1
        for s in range(r+1, 3*q+1):
            tot += 1
            if not any(in_P(X, Y, p, q, r, s) for (X, Y) in Cpts(p, q, r)):
                fail += 1
print(f"  rigidity 2r+p=3q violations: {rig}; completions tested: {tot}; C∩P=∅ failures: {fail}")

# ---- (1,2): rigidity 2r-p=2q; BHK case(a) horiz / case(b) vert / p=2,i=1 ------
# i = s - r >= 1 ; case(a) suffices when p+2i>=6 <=> s >= q+3 ; special p=2,i=1
# => r=q+1, s=q+2.  Check: C∩P!=∅ always, and the length>=spacing sufficient cond.
print("\n=== (1,2)_U : C∩P != ∅ via BHK 5.2.11 (expect all q>=18 ok) ===")
fail = rig = tot = spec = capa = capb = none_len = 0
for q in range(18, 81):
    for p in range(1, q):
        if 3*p >= q or gcd(p, q) != 1: continue
        if (2*q + p) % 2 != 0: continue
        r = (2*q + p)//2
        if not (q < r) or 2*r >= 3*q: continue
        if not is_pair(1, 2, p, q, r): continue
        if 2*r - p != 2*q: rig += 1
        for s in range(r+1, 3*q+1):
            tot += 1
            cp = Cpts(p, q, r)
            exists = any(in_P(X, Y, p, q, r, s) for (X, Y) in cp)
            if not exists: fail += 1
            i = s - r
            x5 = F(q, s)
            hl = (1 - x5)/2                  # BHK case (a) horizontal length
            vl = F(1,6) + (1 - x5)/3         # BHK case (b) vertical length
            # sufficient-condition bookkeeping (which BHK branch certifies it)
            if p == 2 and i == 1:
                spec += 1                    # r=q+1,s=q+2 special (t=j+1/2)
            elif hl >= F(1, q):
                capa += 1                    # horizontal pigeonhole (spacing 1/q)
            elif vl >= F(2, q):
                capb += 1                    # vertical pigeonhole (spacing 2/q)
            else:
                none_len += 1
print(f"  rigidity 2r-p=2q violations: {rig}; completions: {tot}; C∩P=∅ failures: {fail}")
print(f"  BHK branch coverage: case(a) h(l)>=1/q: {capa}; case(b) v(l)>=2/q: {capb};"
      f" p=2,i=1 special: {spec}; NONE: {none_len}")

# ---- p=2,i=1 special: speeds (2,q-2,q,q+1,q+2); t=j+1/2 in 012345-gap ----------
print("\n=== p=2,i=1 special: t=j+1/2 with (2j+1)/q in [1/6,1/3] is a 012345-gap ===")
def circdist(x):
    f = frac(x); return min(f, 1 - f)
bad = 0; checked = 0
for q in range(18, 81):
    if gcd(2, q) != 1: continue              # q odd
    w = [2, q-2, q, q+1, q+2]
    # find j with 1/6 <= (2j+1)/q <= 1/3
    found = False
    for j in range(q):
        if F(1,6) <= F(2*j+1, q) <= F(1,3):
            found = True
            t = F(2*j+1, 2)                  # j + 1/2
            checked += 1
            if not all(circdist(F(wi)*t) >= F(1,6) for wi in w):
                bad += 1
            break
    if not found: print(f"   q={q}: NO valid j (unexpected for q>=9)")
print(f"  checked {checked} odd q in [18,80]; t=j+1/2 NOT a 012345-gap in {bad} of them")
