"""
v3: hunt for an explicit, uniform witness formula for the contrapositive
    q >= 6i  ==>  exists l with C-point P_l in R = [1/6,1/2] x [1/6,1/3].

If a closed-form l(p,q,r,k,i) exists, antidiag_geom becomes a clean "exhibit
witness" proof. We test several candidate constructions and also report the
full witness set structure.

C-point: P_m = (frac(r*m/(2q)), frac(p*m/(2q))), m = 2l+1 odd.
Readoff k:  k*r ≡ i, k*p ≡ -i (mod q).
"""
from math import gcd
from fractions import Fraction as F

def frac(x): return x - (x.numerator//x.denominator)
def P(m,p,q,r): return frac(F(r*m,2*q)), frac(F(p*m,2*q))
XLO,XHI=F(1,6),F(1,2); YLO,YHI=F(1,6),F(1,3)
def inR(X,Y): return XLO<=X<=XHI and YLO<=Y<=YHI
def has_readoff(i,p,q,r):
    for k in range(q):
        if (k*r-i)%q==0 and (k*p+i)%q==0: return k
    return None
def valid_tuples(QMAX):
    for i in (3,4,5):
        for q in range(18,QMAX+1):
            d=gcd(i,q)
            if d==1: continue
            for p in range(1,q):
                if 3*p>=q or gcd(p,q)!=1: continue
                for r in range(q+1,(3*q)//2+1):
                    if 2*r>=3*q: continue
                    k=has_readoff(i,p,q,r)
                    if k is None: continue
                    yield i,p,q,r,d,k

QMAX=120
tuples=list(valid_tuples(QMAX))
print(f"valid tuples up to q={QMAX}: {len(tuples)}")

# For tuples with q>=6i, gather witness m's (odd residues mod 2q).
def witnesses(p,q,r):
    return [m for m in range(1,2*q,2) if inR(*P(m,p,q,r))]

# Candidate formulas for an odd witness m:
#  We want Y=frac(p*m/2q) ~ 1/4  and  X in window.
#  Construction A: choose the odd m minimizing dist of (p*m mod 2q) to q/2 (center y=1/4 -> p*m/2q=1/4 -> p*m mod 2q = q/2).
#  Construction B: use t-grid via k: m = m0 + 2*t*k for best t, m0=1.
def candA(p,q,r):
    best=None;bd=None
    target=F(q,2)  # p*m mod 2q ~ q/2
    for m in range(1,2*q,2):
        val=(p*m)%(2*q)
        dd=abs(F(val)-target)
        if bd is None or dd<bd: bd=dd;best=m
    return best
def candC_centerX(p,q,r):
    # minimize dist of (r*m mod 2q) to q/3 (x-center=1/3 -> r*m mod2q ~ 2q/3)
    best=None;bd=None;target=F(2*q,3)
    for m in range(1,2*q,2):
        val=(r*m)%(2*q); dd=abs(F(val)-target)
        if bd is None or dd<bd: bd=dd;best=m
    return best

q6i=0; A_ok=0; C_ok=0; both_fail=[]
for i,p,q,r,d,k in tuples:
    if q<6*i: continue
    q6i+=1
    W=witnesses(p,q,r)
    assert W, (i,p,q,r)  # H1 guarantees nonempty
    mA=candA(p,q,r); mC=candC_centerX(p,q,r)
    okA= inR(*P(mA,p,q,r)); okC= inR(*P(mC,p,q,r))
    A_ok+=okA; C_ok+=okC
    if not okA and not okC:
        both_fail.append((i,p,q,r,d,k,len(W)))
print(f"q>=6i tuples: {q6i}")
print(f"  candA (Y nearest 1/4) lands in R: {A_ok}/{q6i}")
print(f"  candC (X nearest 1/3) lands in R: {C_ok}/{q6i}")
print(f"  both fail: {len(both_fail)}")
for t in both_fail[:15]: print("    ",t)

# Structure: how many witnesses per tuple, and the m's mod small numbers.
import statistics
counts=[len(witnesses(p,q,r)) for i,p,q,r,d,k in tuples if q>=6*i]
print(f"\nwitness-count per q>=6i tuple: min={min(counts)} max={max(counts)} mean={statistics.mean(counts):.2f}")

# Does the *number of witnesses* grow with q (slack)? show the tight ones (count<=2).
tight=[(i,p,q,r,d,witnesses(p,q,r)) for i,p,q,r,d,k in tuples if q>=6*i and len(witnesses(p,q,r))<=2]
print(f"tight tuples (<=2 witnesses) among q>=6i: {len(tight)}")
for i,p,q,r,d,W in tight[:25]:
    ms=W
    print(f"   i={i} p={p} q={q} r={r} d={d} 6i={6*i} witness m={ms}  P={[ (str(a),str(b)) for a,b in (P(m,p,q,r) for m in ms)]}")
