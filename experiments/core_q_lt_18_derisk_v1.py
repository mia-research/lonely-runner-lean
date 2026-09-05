from math import gcd
from fractions import Fraction as F

# C-point at half-integer index l: X = fract(r*(2l+1)/(2q)), Y = fract(p*(2l+1)/(2q))
# Rectangle R: X in [1/6,1/2], Y in [1/6,1/3]
def fract(num, den):
    return F(num % den, den)

def Cpoints(p, q, r):
    den = 2*q
    pts = []
    for l in range(2*q):  # period 2q
        X = fract(r*(2*l+1), den)
        Y = fract(p*(2*l+1), den)
        pts.append((l, X, Y))
    return pts

def in_R(X, Y):
    return F(1,6) <= X <= F(1,2) and F(1,6) <= Y <= F(1,3)

# conservative pentagon P\R upper bound (BHK (51)), s-independent, for 1/6<=Y<=1/3:
#   X <= 1 + min(3(Y-1/6), 1/3 - Y)
# and we require it to be a *gap* extension to the right of R, so X > 1/2.
# lower edge: the segment from R extends; we use Y in [1/6,1/3], X in (1/2, bound].
def in_consP_minus_R(X, Y):
    if not (F(1,6) <= Y <= F(1,3)):
        return False
    bound = 1 + min(3*(Y-F(1,6)), F(1,3)-Y)
    return F(1,2) < X <= bound

rows = []
for q in range(5,18):
    for p in range(1, q):
        if 3*p >= q: continue
        if gcd(p,q)!=1: continue
        for r in range(q+1, 2*q):
            if gcd(r,q)!=1: continue
            diagonal = (r == p+q)
            pts = Cpoints(p,q,r)
            hitsR = any(in_R(X,Y) for (_,X,Y) in pts)
            v1_big = 6*p > q  # v1 > 1/6
            hitsP = any(in_consP_minus_R(X,Y) for (_,X,Y) in pts)
            status = "R" if hitsR else ("P" if (hitsP and v1_big) else ("DIAG" if diagonal else "??NEEDS_V5"))
            rows.append((q,p,r,diagonal,hitsR,v1_big,hitsP,status))

from collections import Counter
c = Counter(row[7] for row in rows)
print("total triples:", len(rows))
print("status counts:", dict(c))
print()
print("Triples NOT killed by R (need P/DIAG/V5):")
for row in rows:
    if row[7] != "R":
        q,p,r,diag,hitsR,v1big,hitsP,st = row
        print(f"  q={q} p={p} r={r} diag={diag} v1>1/6={v1big} hitsConsP={hitsP} -> {st}")
