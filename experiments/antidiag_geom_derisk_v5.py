"""
v5: Does adding BHK's bound (50) v4 < (6+i)/(2|j|) rescue the clean argument?

For anti-diagonal (i,-i): |j|=i, so (50) is v4 = r/q < 3/i + 1/2,
i.e. 2*i*r < (6+i)*q.  (My earlier hr32 was only 2r<3q = v4<3/2.)

Hypothesis to test: with (50) added, for EVERY surviving tuple, the coset's
S-points actually occupy a slope-(-1) line c0 = X+Y in [1/2,2/3] that crosses R
with FULL vertical length 1/6 -- i.e. BHK's stated argument is sufficient.

Checks:
 (1) Is (1,24,35) and the whole v2 "nofull" list excluded by (50)?
 (2) Among tuples with (50), q>=6i: is there ALWAYS a witness on a full-1/6 circle?
 (3) What is the on-circle grid spacing on the full-1/6 circle, and is it <= 1/6
     (so grid_hit guarantees the witness)?  Report spacing structure.
 (4) Re-confirm soundness: (50) + C∩R=∅ => q<6i and i|q.
"""
from math import gcd
from fractions import Fraction as F

def frac(x): return x - (x.numerator//x.denominator)
def S(l,p,q,r): u=2*l+1; return frac(F(r*u,2*q)), frac(F(p*u,2*q))
XLO,XHI=F(1,6),F(1,2); YLO,YHI=F(1,6),F(1,3)
def inR(X,Y): return XLO<=X<=XHI and YLO<=Y<=YHI
def has_readoff(i,p,q,r):
    for k in range(q):
        if (k*r-i)%q==0 and (k*p+i)%q==0: return k
    return None
def bound50(i,p,q,r):  # v4 < (6+i)/(2i)  <=>  2*i*r < (6+i)*q
    return 2*i*r < (6+i)*q
def valid_tuples(QMAX, use50):
    for i in (3,4,5):
        for q in range(18,QMAX+1):
            d=gcd(i,q)
            if d==1: continue
            for p in range(1,q):
                if 3*p>=q or gcd(p,q)!=1: continue
                for r in range(q+1,(3*q)//2+1):
                    if 2*r>=3*q: continue
                    if use50 and not bound50(i,p,q,r): continue
                    k=has_readoff(i,p,q,r)
                    if k is None: continue
                    yield i,p,q,r,d,k

def full_cross(c0):  # line x+y=c0 crosses S-window R with full vertical length 1/6 ?
    for sh in (c0, c0+1):
        lo=max(YLO, sh-XHI); hi=min(YHI, sh-XLO)
        if hi-lo==F(1,6): return True
    return False

QMAX=120

# (1) is the v2 nofull list excluded?
print("=== (1) are the old problem tuples excluded by (50)? ===")
for (i,p,q,r) in [(4,1,24,35),(4,5,24,31),(4,7,24,29),(4,1,26,38),(4,1,28,41),(5,1,30,44) if False else (4,1,30,44)]:
    print(f"  ({i},{p},{q},{r}): v4={F(r,q)}={float(F(r,q)):.3f}  (50) bound 3/i+1/2={F(3,i)+F(1,2)}  passes(50)? {bound50(i,p,q,r)}")

# (2)+(3): with (50), check witness on a full-1/6 circle, and spacing.
print("\n=== (2)+(3) with (50): witness on full-1/6 circle? spacing? ===")
n=0; have_fullwit=0; fail=[]
spacings=set()
for i,p,q,r,d,k in valid_tuples(QMAX, use50=True):
    if q<6*i: continue
    n+=1
    wit=[l for l in range(2*q) if inR(*S(l,p,q,r))]
    # witnesses on a full-1/6 circle:
    fw=[l for l in wit if full_cross(frac(F((r+p)*(2*l+1),2*q)))]
    if fw: have_fullwit+=1
    else: fail.append((i,p,q,r,d,k,wit[:2]))
    # spacing on the circle of the (first) witness: e=gcd(r+p,q), spacing p/e in Y
    e=gcd(r+p,q); spacings.add(F(p,e))
print(f"  (50)+q>=6i tuples: {n}")
print(f"  with a witness on a FULL-1/6 circle: {have_fullwit}/{n}; fails={len(fail)}")
for t in fail[:20]: print("    FAIL:",t)
print(f"  distinct on-circle Y-spacings p/gcd(r+p,q): {sorted(spacings)[:20]}  (max={max(spacings)})")

# (4) soundness under (50): does C∩R=∅ still occur, and q<6i & i|q hold?
print("\n=== (4) soundness with (50) ===")
empt=[]
for i,p,q,r,d,k in valid_tuples(QMAX, use50=True):
    if all(not inR(*S(l,p,q,r)) for l in range(2*q)):
        empt.append((i,p,q,r,d, q<6*i, q%i==0))
print(f"  C∩R-empty tuples under (50): {len(empt)}")
for t in empt: print("    ",t)

# Also: does (50) hold for ALL q<6i too (i.e. is the empty set exactly characterized)?
# And what's the relation: under (50), is q<6i automatic or still needs the witness?
print("\n=== bonus: under (50), distribution of q vs 6i for q>=6i tuples (are there any?) ===")
cnt_ge=sum(1 for i,p,q,r,d,k in valid_tuples(QMAX,use50=True) if q>=6*i)
cnt_all=sum(1 for _ in valid_tuples(QMAX,use50=True))
print(f"  tuples with (50): {cnt_all}; of which q>=6i: {cnt_ge}")
