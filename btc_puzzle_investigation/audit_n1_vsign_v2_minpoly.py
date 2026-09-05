#!/usr/bin/env python3
"""Exact minimal polynomial of e2(1) in Z[zeta_n], and the mu6 orbit structure.
No floats in the signal path; float only in the final human-readable root printout
(clearly marked, decides nothing)."""
import sys
from fractions import Fraction
sys.path.insert(0,"/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from audit_n1_vsign_v2_core import compute_e2_poly, is_prime

def red(A,n):
    """vector length n (mod x^n-1) -> length n-1 (mod Phi_n), n prime"""
    c = A[n-1]
    return [A[i]-c for i in range(n-1)]

def mulF(A,B,n):
    """multiply in Z[x]/Phi_n, inputs/outputs length n-1"""
    C = [0]*(2*n-3)
    for i,ai in enumerate(A):
        if ai==0: continue
        for j,bj in enumerate(B):
            if bj==0: continue
            C[i+j]+=ai*bj
    # reduce mod x^n - 1 first
    D=[0]*n
    for i,c in enumerate(C): D[i%n]+=c
    return red(D,n)

def sig(A,c,n):
    """sigma_c on length-(n-1) vector: zeta -> zeta^c"""
    D=[0]*n
    for i,ai in enumerate(A): D[(i*c)%n]+=ai
    return red(D,n)

def mu6(n):
    """the order-6 subgroup of (Z/n)^*"""
    g=2
    while True:
        # find element of order 6
        ok=False
        for m in range(2,n):
            if pow(m,6,n)==1 and pow(m,3,n)!=1 and pow(m,2,n)!=1:
                z=m; ok=True; break
        assert ok
        return sorted({pow(z,i,n) for i in range(6)})

def analyse(p,verbose=True):
    n,h1,h2,W = compute_e2_poly(p)
    Wr = red(W,n)                 # 2*e2(1) in basis 1..zeta^{n-2}
    M = mu6(n)
    # mu6 invariance check (exact)
    inv = all(sig(Wr,m,n)==Wr for m in M)
    # coset representatives of mu6 in (Z/n)^*
    seen=set(); reps=[]
    for a in range(1,n):
        if a in seen: continue
        orb={a*m%n for m in M}
        seen|=orb; reps.append(a)
    # min poly of e2(1) = Wr/2 : prod over reps (Y - e2(rep)), coefficients in Z[x]/Phi_n
    one=[1]+[0]*(n-2)
    poly=[one]        # coefficient list, poly[i] multiplies Y^i ; start with 1
    for a in reps:
        t = sig(Wr,a,n)                       # = 2*e2(a)
        # multiply current poly by (Y - t/2) -> keep track of factor 2^k : use 2Y' ... simpler: use Fractions
        new=[[0]*(n-1) for _ in range(len(poly)+1)]
        for i,co in enumerate(poly):
            for j in range(n-1): new[i+1][j]+=co[j]           # Y * co
        for i,co in enumerate(poly):
            pr = mulF(co,t,n)
            for j in range(n-1): new[i][j] -= pr[j]           # - (2 e2(a)) * co  (scaled)
        poly=new
    # poly is prod (Y - 2 e2(a)) ; substitute Y = 2X to get prod 2*(X - e2(a)) = 2^d * m(X)
    d=len(poly)-1
    coeffs=[]
    for i,co in enumerate(poly):
        # co must be a rational integer: only constant term nonzero
        assert all(x==0 for x in co[1:]), f"coefficient {i} not rational: {co[:5]}"
        c=co[0]
        # Y^i -> 2^i X^i ; then divide overall by 2^d
        num = c*(2**i)
        assert num % (2**d)==0
        coeffs.append(num//(2**d))
    # coeffs[i] = coefficient of X^i in m_p(X)
    return dict(p=p,n=n,d=d,mu6_invariant=inv,reps=reps,minpoly=coeffs,W=Wr,mu6=M)

if __name__=="__main__":
    for p in (13,43):
        r=analyse(p)
        print(f"p={r['p']}  n={r['n']}  deg=(n-1)/6={r['d']}  mu6={r['mu6']}  mu6-invariant(exact)={r['mu6_invariant']}")
        c=r['minpoly']
        terms=" + ".join(f"{c[i]}*Y^{i}" for i in range(len(c)-1,-1,-1) if c[i]!=0)
        print("  m_p(Y) =",terms)
        print("  coeff list (low->high):",c)
