#!/usr/bin/env python3
"""Exact M3c / M3d evaluation, and the v-criterion, as TOTAL NON-NEGATIVITY of
explicit elements of Z[zeta_n].  All integer arithmetic; Sturm (exact rationals)
counts the offending conjugates."""
import sys, time
sys.path.insert(0,"/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from audit_n1_vsign_v2_core import compute_e2_poly, polymul_mod_cyc
from audit_n1_vsign_v2_minpoly import red, mulF, sig, mu6
import sympy as sp

def minpoly_of(vec, n, scale=1):
    """vec: length-(n-1) integer vector = the element (times `scale`) in Z[zeta_n].
    Returns sympy Poly in Y whose roots are the conjugates of vec/scale."""
    M = mu6(n)
    assert all(sig(vec,m,n)==vec for m in M), "element is not mu6-invariant"
    seen=set(); reps=[]
    for a in range(1,n):
        if a in seen: continue
        seen |= {a*m%n for m in M}; reps.append(a)
    one=[1]+[0]*(n-2)
    poly=[one]
    for a in reps:
        t=sig(vec,a,n)
        new=[[0]*(n-1) for _ in range(len(poly)+1)]
        for i,co in enumerate(poly):
            for j in range(n-1): new[i+1][j]+=co[j]
        for i,co in enumerate(poly):
            pr=mulF(co,t,n)
            for j in range(n-1): new[i][j]-=pr[j]
        poly=new
    d=len(poly)-1
    cs=[]
    for i,co in enumerate(poly):
        assert all(x==0 for x in co[1:]), "not rational"
        cs.append(co[0]*scale**(d-i))          # roots divided by `scale`
    Y=sp.Symbol('Y')
    return sp.Poly(sum(cs[i]*Y**i for i in range(d+1)), Y), d

def const(c,n):
    return [c]+[0]*(n-2)

def report(p):
    n,h1,h2,W = compute_e2_poly(p)
    Wr = red(W,n)                      # 2*e2
    X  = red(polymul_mod_cyc(h1,h1,n), n)   # V1^2
    d=(n-1)//6
    sin_ = (p%4==3)
    print(f"\n===== p={p}  n={n}  d=(n-1)/6={d}  stratum={'SIN' if sin_ else 'COS'} =====")
    tests={}
    if sin_:
        # v <= 0  <=>  e2 + 2p >= 0  <=>  W + 4p >= 0
        tests['v<=0  : W+4p']      = [Wr[i]+ (4*p if i==0 else 0) for i in range(n-1)]
        tests['M3c-a : 4p-W']      = [(4*p if i==0 else 0)-Wr[i] for i in range(n-1)]
        A=[(4*p if i==0 else 0)-Wr[i] for i in range(n-1)]
        A2=mulF(A,A,n)
        tests['M3c-b : (4p-W)^2+16pX'] = [A2[i]+16*p*X[i] for i in range(n-1)]
        tests['M3d-a : 2W+8p-X']   = [2*Wr[i]+(8*p if i==0 else 0)-X[i] for i in range(n-1)]
        tests['M3d-b : X+16p']     = [X[i]+(16*p if i==0 else 0) for i in range(n-1)]
    else:
        # v <= 0 <=> e2 - 2p <= 0 <=> 4p - W >= 0
        tests['v<=0  : 4p-W']      = [(4*p if i==0 else 0)-Wr[i] for i in range(n-1)]
        # COS: u^2 = X/(4p),  v=(W-4p)/(8p), 1+v=(4p+W)/(8p)
        tests['M3c-a : 4p+W']      = [Wr[i]+(4*p if i==0 else 0) for i in range(n-1)]
        A=[Wr[i]+(4*p if i==0 else 0) for i in range(n-1)]
        A2=mulF(A,A,n)
        tests['M3c-b : (4p+W)^2-16pX'] = [A2[i]-16*p*X[i] for i in range(n-1)]
        tests['M3d-a : X-2W+8p']   = [X[i]-2*Wr[i]+(8*p if i==0 else 0) for i in range(n-1)]
        tests['M3d-b : 16p-X']     = [(16*p if i==0 else 0)-X[i] for i in range(n-1)]
    for name,vec in tests.items():
        t0=time.time()
        P,dd = minpoly_of(vec,n)
        neg = P.count_roots(None, sp.Integer(0))   # roots <= 0
        strict = P.count_roots(None, sp.Integer(-1))
        nreal = len(P.real_roots())
        print(f"  {name:28s} deg={dd:4d} totally_real={nreal==dd}  #conj <= 0 : {neg}"
              f"   ({time.time()-t0:.1f}s)")
    return n,d

if __name__=="__main__":
    for p in [int(x) for x in sys.argv[1].split(",")]:
        report(p)
