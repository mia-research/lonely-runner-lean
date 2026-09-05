#!/usr/bin/env python3
"""
_audit_ct_and_xy_v1.py -- audit two dismissals for the negative-bias failure mode.

AUDIT 1 (C_T '2-3% is finite-n, mechanism refuted'). The shear refutation (lambda2=lambda3=1/3
EXACT under the uniform model) is solid. But my claim 'the 2-3% is finite-n' rested on a 4-point
decay whose fitted exponent (-0.279) did NOT match DRILL 01 (-0.584) -- I leaned on their number.
Audit: get MANY (n, |l2-l3|) points from MY data and fit the exponent honestly. If it is clean and
negative, 'finite-n' is earned; if not, I must flag it.

AUDIT 2 (x/y 'at the floor, captures no fraction of the 0.93 shadow'). x/y is a JOINT readout. I
compared it only to the x-only floor. CHARACTERIZE what it captures: does R=x/y correlate with the
KNOWN shadow bit sign(x*y) (the D-shadow, v33) and with y-parity? 'At the floor for the DLP-aligned
metric' and 'captures the known cheap shadow' are different statements; I conflated them.

Exact modular ints in the signal path; float only for spectral eigenvalues / correlation magnitude.
"""
import sys, math, cmath
import numpy as np
from sympy import isprime
from sympy.ntheory.residue_ntheory import sqrt_mod
from lift_sextant_rhombus_law_proof_v2 import reduced_basis, rdiv

# ---------------- AUDIT 1: C_T split decay, many primes, honest fit ----------------
def ct_split(p):
    R1, R2 = reduced_basis(p)
    if R1 is None: return None
    DET = R1[0]*R2[1]-R1[1]*R2[0]
    def add(A,B):
        if A is None: return B
        if B is None: return A
        x1,y1=A; x2,y2=B
        if x1==x2:
            if (y1+y2)%p==0: return None
            lam=(3*x1*x1)*pow(2*y1,-1,p)%p
        else: lam=(y2-y1)*pow(x2-x1,-1,p)%p
        x3=(lam*lam-x1-x2)%p
        return (x3,(lam*(x1-x3)-y1)%p)
    def eis(X):
        c1=rdiv(X*R2[1],DET); c2=rdiv(-X*R1[1],DET)
        return (X-(c1*R1[0]+c2*R2[0]), -(c1*R1[1]+c2*R2[1]))
    def st(z1,z2):
        sx,sy=z1[0]+z2[0],z1[1]+z2[1]
        return (rdiv(sx*R2[1]-sy*R2[0],DET), rdiv(-sx*R1[1]+sy*R1[0],DET))
    G=None
    for x in range(1,p):
        if pow((x*x*x+7)%p,(p-1)//2,p)==1:
            y=sqrt_mod((x*x*x+7)%p,p)
            if y: G=(x,int(y)); break
    if G is None: return None
    pts=[G]; cur=G
    while True:
        cur=add(cur,G)
        if cur is None: break
        pts.append(cur)
    n=len(pts)
    z=[eis(P[0]) for P in pts]
    seq=[st(z[k],z[k+1]) for k in range(n-1)]
    S9=[(a,b) for a in (-1,0,1) for b in (-1,0,1)]; I9={s:i for i,s in enumerate(S9)}
    C=np.zeros((9,9))
    for a,b in zip(seq[:-1],seq[1:]):
        if a in I9 and b in I9: C[I9[a],I9[b]]+=1
    rs=C.sum(1,keepdims=True); rs[rs==0]=1
    T=C/rs
    ev=sorted((abs(e) for e in np.linalg.eigvals(T)),reverse=True)
    return n, abs(ev[1]-ev[2])

def audit1():
    print("="*70); print("AUDIT 1 -- C_T |lambda2-lambda3| decay (is 'finite-n' earned?)"); print("="*70)
    data=[]
    for p in range(1000, 60000):
        if p%6!=1 or not isprime(p): continue
        r=ct_split(p)
        if r and isprime(r[0]+1-(p+1-r[0]))  or True:
            if r: data.append(r)
        if len(data)>=9: break
    print(f"  {'n':>7} {'|l2-l3|':>9}")
    for n,s in data: print(f"  {n:>7} {s:>9.4f}")
    xs=[math.log(n) for n,_ in data]; ys=[math.log(s) for _,s in data if s>0]
    xs=xs[:len(ys)]
    k=len(xs); sx=sum(xs); sy=sum(ys); sxx=sum(x*x for x in xs); sxy=sum(x*y for x,y in zip(xs,ys))
    b=(k*sxy-sx*sy)/(k*sxx-sx*sx)
    # correlation coefficient of the fit
    my=sy/k; mx=sx/k
    ssxy=sum((x-mx)*(y-my) for x,y in zip(xs,ys)); ssxx=sum((x-mx)**2 for x in xs); ssyy=sum((y-my)**2 for y in ys)
    rcorr=ssxy/math.sqrt(ssxx*ssyy) if ssxx*ssyy>0 else 0
    print(f"\n  FITTED exponent b = {b:.3f}   (DRILL 01 claimed -0.584; my earlier 4-pt fit was -0.279)")
    print(f"  log-log correlation r = {rcorr:.3f}  ({'clean power-law decay -> finite-n EARNED' if rcorr<-0.9 else 'NOT a clean decay -> finite-n NOT cleanly shown by my data'})")

# ---------------- AUDIT 2: what does x/y actually capture? ----------------
def audit2():
    print("\n"+"="*70); print("AUDIT 2 -- x/y readout: characterize what it captures (not just 'floor')"); print("="*70)
    for p in (211, 433, 733, 1051, 1669):
        if not isprime(p) or p%6!=1: continue
        # build G-order points
        def add(A,B):
            if A is None: return B
            if B is None: return A
            x1,y1=A; x2,y2=B
            if x1==x2:
                if (y1+y2)%p==0: return None
                lam=(3*x1*x1)*pow(2*y1,-1,p)%p
            else: lam=(y2-y1)*pow(x2-x1,-1,p)%p
            x3=(lam*lam-x1-x2)%p
            return (x3,(lam*(x1-x3)-y1)%p)
        G=None
        for x in range(1,p):
            if pow((x*x*x+7)%p,(p-1)//2,p)==1:
                y=sqrt_mod((x*x*x+7)%p,p)
                if y: G=(x,int(y)); break
        pts=[G]; cur=G
        while True:
            cur=add(cur,G)
            if cur is None: break
            pts.append(cur)
        n=len(pts)
        if not isprime(n): continue
        xG,yG=G; inv=lambda t: pow(t,p-2,p); halfp=(p-1)//2
        R=[(x*yG%p)*inv(y*xG%p)%p for (x,y) in pts]          # the x/y readout value
        # known shadow bit: sign(x*y) (v33, the odd-in-d mu3-covariant D-shadow)
        sgn_xy=[1 if (x*y%p)<=halfp else -1 for (x,y) in pts]
        sy=[1 if y<=halfp else -1 for (x,y) in pts]           # y-parity (the free odd bit)
        # does R (as an F_p value) determine / correlate with these cheap bits?
        # exact test: is sign(R centered) == some function of sgn_xy or sy? mutual agreement rate.
        Rsign=[1 if r<=halfp else -1 for r in R]
        ag_xy=sum(1 for a,b in zip(Rsign,sgn_xy) if a==b)/n
        ag_sy=sum(1 for a,b in zip(Rsign,sy) if a==b)/n
        # and: is R itself simply related to a known object? R = x/y; x/y vs x*y?
        print(f"  p={p:>5} n={n:>5}: sign(x/y) agrees with sign(xy) {ag_xy:.3f}, with y-parity {ag_sy:.3f}"
              f"  (0.5 = independent)")
    print("  => characterizes WHAT x/y is, vs the vague 'at the floor'. Agreement != 0.5 would mean")
    print("     x/y carries the known cheap shadow bit (structure), even though its DLP-aligned")
    print("     correlation is at the sqrt(p) floor. Two different statements I had conflated.")

if __name__ == '__main__':
    audit1()
    audit2()
