"""
De-risk BHK Case 5.2.2 (anti-diagonal grid geometry) before Lean formalization.

Setup (matching bhk_prop11_antidiag_geom):
  i in {3,4,5}, q>=18, gcd(p,q)=1, q<r, 2r<3q (so q<r<3q/2), 0<p, 3p<q.
  Readoff: exists k with  k*r ≡ i (mod q)  and  k*p ≡ -i (mod q).
  Anti-diagonal pair (i,j)=(i,-i), gcd(i,q)=d>1 (non-coprime branch).

S-points (what h_nogood constrains):
  X_l = frac(r/q*(l+1/2)) = frac(r*(2l+1)/(2q))
  Y_l = frac(p/q*(l+1/2)) = frac(p*(2l+1)/(2q))
R-window (for S):  X in [1/6,1/2], Y in [1/6,1/3].
h_nogood = "C∩R=∅" = for all l, NOT (X_l in xwin and Y_l in ywin).

Claim to test (BHK): C∩R=∅  ==>  q < 6i  and  i|q.
My proposed proof route gives instead q < 6d (d=gcd(i,q)) via a grid-avoid on
spacing d/q, using the circle c0 = frac((r+p)(2l+1)/(2q)) in [1/2,2/3].

Questions:
 Q1. For every valid tuple with C∩R=∅, is q < 6i true? is i|q true?  (lemma soundness)
 Q2. For tuples with q >= 6d (d=gcd), is C∩R always NONEMPTY (witness exists)? (reduction q<6d correctness)
 Q3. When a witness exists, is its circle c0 in [1/2,2/3]? If not, what circle works?
"""
from math import gcd
from fractions import Fraction as F

def frac(x: F) -> F:
    return x - (x.numerator // x.denominator)

def in_icc(x: F, a: F, b: F) -> bool:
    return a <= x <= b

XWIN = (F(1,6), F(1,2))
YWIN = (F(1,6), F(1,3))

def S(l, p, q, r):
    u = 2*l + 1
    return frac(F(r*u, 2*q)), frac(F(p*u, 2*q))

def cap_R_empty(p, q, r):
    """Return None if C∩R empty over a full period of l, else a witness l (in [0,2q))."""
    # period of (X_l,Y_l) in l is 2q (since 2l+1 mod 2q determines both, and l->l+q gives 2l+1 -> +2q).
    for l in range(0, 2*q):
        X, Y = S(l, p, q, r)
        if in_icc(X, *XWIN) and in_icc(Y, *YWIN):
            return l
    return None

def has_readoff(i, p, q, r):
    """Return a k in [0,q) with k*r ≡ i and k*p ≡ -i (mod q), else None."""
    for k in range(q):
        if (k*r - i) % q == 0 and (k*p + i) % q == 0:
            return k
    return None

def c0_of(l, p, q, r):
    u = 2*l+1
    return frac(F((r+p)*u, 2*q))

bad_soundness = []   # C∩R empty but q>=6i  (would make lemma FALSE)
bad_dvd = []         # C∩R empty but not i|q
reduction_fail = []  # q >= 6d but C∩R NONempty -> good for reduction; we want to confirm q>=6d => nonempty
red_ok = 0
witness_circles = []  # (i,p,q,r, c0 of witness, in[1/2,2/3]?)
n_empty = 0
n_tuples = 0

QMAX = 80
for i in (3,4,5):
    for q in range(18, QMAX+1):
        d = gcd(i, q)
        if d == 1:
            continue  # non-coprime branch only
        for p in range(1, q):
            if 3*p >= q:        # need 3p<q
                continue
            if gcd(p, q) != 1:
                continue
            for r in range(q+1, (3*q+1)//2 + 1):
                if 2*r >= 3*q:  # need 2r<3q strict
                    continue
                k = has_readoff(i, p, q, r)
                if k is None:
                    continue
                n_tuples += 1
                w = cap_R_empty(p, q, r)
                if w is None:
                    # C∩R empty -> h_nogood holds. Check conclusions.
                    n_empty += 1
                    if not (q < 6*i):
                        bad_soundness.append((i,p,q,r,d,k))
                    if q % i != 0:
                        bad_dvd.append((i,p,q,r,d,k))
                else:
                    # witness exists -> C∩R nonempty.
                    if q >= 6*d:
                        red_ok += 1
                    c0 = c0_of(w, p, q, r)
                    witness_circles.append((i,p,q,r,d,c0, F(1,2) <= c0 <= F(2,3)))

print(f"tuples examined: {n_tuples}, with C∩R empty: {n_empty}")
print(f"Q1 soundness violations (C∩R empty but q>=6i): {len(bad_soundness)}")
for t in bad_soundness[:20]:
    print("   ", t)
print(f"Q1b divisibility violations (C∩R empty but not i|q): {len(bad_dvd)}")
for t in bad_dvd[:20]:
    print("   ", t)

# Q2: among tuples with q>=6d, how many had C∩R empty (should be 0 for reduction q<6d to be valid)?
q_ge_6d_empty = [(i,p,q,r,d,k) for (i,p,q,r,d,k) in bad_soundness]  # placeholder
# recompute cleanly:
viol_red = []
for i in (3,4,5):
    for q in range(18, QMAX+1):
        d = gcd(i,q)
        if d==1: continue
        for p in range(1,q):
            if 3*p>=q or gcd(p,q)!=1: continue
            for r in range(q+1,(3*q)//2+1):
                if 2*r>=3*q: continue
                if has_readoff(i,p,q,r) is None: continue
                if q >= 6*d and cap_R_empty(p,q,r) is None:
                    viol_red.append((i,p,q,r,d))
print(f"Q2 reduction violations (q>=6d but C∩R EMPTY): {len(viol_red)}")
for t in viol_red[:20]:
    print("   ", t)

# Q3: witness circle distribution
print(f"\nQ3 witnesses recorded: {len(witness_circles)}")
in_band = sum(1 for *_, ok in witness_circles if ok)
print(f"   witness circle c0 in [1/2,2/3]: {in_band}/{len(witness_circles)}")
# show some where NOT in band
notband = [w for w in witness_circles if not w[-1]]
print(f"   witnesses with c0 NOT in [1/2,2/3]: {len(notband)} (sample:)")
for t in notband[:15]:
    print("   ", t[:5], "c0=", t[5], float(t[5]))
