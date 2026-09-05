"""
v2: nail the actual structure of BHK Case 5.2.2 anti-diagonal witnesses.

Findings from v1: lemma is SOUND (0 violations), q>=6d => C∩R nonempty (0 viol),
but spacing assumption was wrong. Only 1 tuple in [18,80] has C∩R empty.

Goals here:
 (A) Identify the surviving C∩R-empty tuple(s) and their (i,p,q,r,d).
 (B) For each tuple, find ALL witnesses (l in [0,2q)) and characterize:
       - circle c0 = frac((r+p)(2l+1)/(2q))
       - which circles actually cross R, and the crossing's vertical length.
       - the Y-spacing of S-points on a single circle.
 (C) Determine the correct uniform reduction: is the right bound q<6i (BHK) and
     does "q >= 6i => witness on a FULL-length-1/6 crossing" hold? i.e. is there
     always a witness whose circle has a full 1/6 crossing when q>=6i?
"""
from math import gcd
from fractions import Fraction as F

def frac(x): return x - (x.numerator // x.denominator)
def S(l,p,q,r):
    u=2*l+1
    return frac(F(r*u,2*q)), frac(F(p*u,2*q))
XLO,XHI=F(1,6),F(1,2)
YLO,YHI=F(1,6),F(1,3)
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

QMAX=80
# (A) surviving empty tuples
print("=== (A) C∩R EMPTY tuples ===")
empties=[]
for i,p,q,r,d,k in valid_tuples(QMAX):
    if all(not inR(*S(l,p,q,r)) for l in range(2*q)):
        empties.append((i,p,q,r,d,k))
        print(f"  i={i} p={p} q={q} r={r} d=gcd(i,q)={d} k={k}  q<6i? {q<6*i}  i|q? {q%i==0}")
print(f"  total empty: {len(empties)}")

# (C) the key reduction test with the CORRECT bound.
# For each tuple, compute: min over witnesses of (crossing structure).
# Test hypotheses H1: q>=6i => witness exists.  H2: q>=6i => witness on a circle with full 1/6 crossing.
print("\n=== (C) reduction bound tests ===")
def crossing_vlen(c0):
    """vertical length of intersection of line x+y=c0 (mod1) with R, taking the
    relevant branch; returns the max over integer shifts of c0."""
    best=F(0)
    for shift in (c0, c0+1):
        # y in [max(YLO, shift-XHI), min(YHI, shift-XLO)]
        lo=max(YLO, shift-XHI); hi=min(YHI, shift-XLO)
        if hi>lo: best=max(best,hi-lo)
    return best

viol_H1_6i=[]; viol_H1_6d=[]
full_cross_when_6i=0; tot_6i=0
no_full_cross_6i=[]
for i,p,q,r,d,k in valid_tuples(QMAX):
    wit=[l for l in range(2*q) if inR(*S(l,p,q,r))]
    if q>=6*i:
        tot_6i+=1
        if not wit: viol_H1_6i.append((i,p,q,r,d))
        # does some witness lie on a circle with full 1/6 crossing?
        circles_with_full=set()
        for l in wit:
            u=2*l+1; c0=frac(F((r+p)*u,2*q))
            if crossing_vlen(c0)==F(1,6): circles_with_full.add(c0)
        if circles_with_full: full_cross_when_6i+=1
        else: no_full_cross_6i.append((i,p,q,r,d,wit[:1]))
    if q>=6*d and not wit:
        viol_H1_6d.append((i,p,q,r,d))
print(f"H1 (q>=6i => witness): violations={len(viol_H1_6i)} / {tot_6i}")
print(f"H1 (q>=6d => witness): violations={len(viol_H1_6d)}")
print(f"H2 (q>=6i => some witness on FULL-1/6-crossing circle): {full_cross_when_6i}/{tot_6i}; fails={len(no_full_cross_6i)}")
for t in no_full_cross_6i[:15]: print("   nofull:",t)

# (B) structure detail for a few representative tuples incl boundary d=4 s=6 and empties
print("\n=== (B) structure detail (sample) ===")
def detail(i,p,q,r):
    d=gcd(i,q); e=gcd(r+p,q)
    wit=[l for l in range(2*q) if inR(*S(l,p,q,r))]
    # Y-spacing on a single circle: consecutive same-circle l differ by q/e; Ystep=(q/e)*p/q=p/e
    print(f"  i={i} p={p} q={q} r={r}: d={d} e=gcd(r+p,q)={e} p/e={F(p,e)} d/q={F(d,q)} i/q={F(i,q)} #wit={len(wit)} q<6i={q<6*i} q<6d={q<6*d}")
    if wit:
        cs=sorted(set(frac(F((r+p)*(2*l+1),2*q)) for l in wit))
        print(f"      witness circles c0: {[str(c) for c in cs]}")
for t in [(4,1,24,35),(4,1,20,29),(3,1,33,43),(4,1,18,26)]+[(e[0],e[1],e[2],e[3]) for e in empties]:
    detail(*t)
