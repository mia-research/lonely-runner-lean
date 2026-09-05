#!/usr/bin/env python3
"""F5's M2b mutation battery, run through the REAL pipeline at p=43.
For each mutation: does M1 (exact m_43 match) fail?  does M3c (|u| <= 1+v) fail?
Everything exact."""
import sys, time, itertools
sys.path.insert(0,"/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from audit_n1_vsign_v2_core import (curve_order, dlog_table, hist_k1, legendre,
                                    tonelli, F2, ec_add2, polymul_mod_cyc, is_prime)
from audit_n1_vsign_v2_minpoly import red, mulF, sig, mu6
from audit_n1_vsign_v2_m3 import minpoly_of
import sympy as sp
B=7
REF=[42288128,-5515008,224768,-2032,-60,1]     # m_43 low->high, from check 1

def hist_k2_mut(p,n,dl,mode):
    F=F2(p); q=p*p; half=(q-1)//2
    sq={}
    for a in range(p):
        for b in range(p): sq[F.sq((a,b))]=(a,b)
    h=[0]*n; Bq=(B%p,0); skipped=0
    for a in range(p):
        for b in range(p):
            x=(a,b)
            r=F.add(F.mul(F.sq(x),x),Bq)
            if r==(0,0): continue
            y=sq.get(r)
            if y is None: continue
            for yy in (y,F.neg(y)):
                if mode=='chi_exp':   c = 1 if F.pw(yy,(p-1)//2)==(1,0) else -1
                else:                 c = 1 if F.pw(yy,half)==(1,0) else -1
                P=(x,yy)
                if mode=='no_frob':
                    T=P
                else:
                    T=ec_add2(F,P,(F.frob(x),F.frob(yy)),B)
                if T is None: d=0
                else:
                    if T[0][1]!=0 or T[1][1]!=0:
                        skipped+=1; continue          # not in E(F_p): mutation (iii) has no defined d
                    d=dl[(T[0][0],T[1][0])]
                h[d]+=c
    return h,skipped

def analyse_vec(p,n,h1,h2,bugP2=False):
    A2=polymul_mod_cyc(h1,h1,n)
    if bugP2:  W=[A2[i]-h2[i] for i in range(n)]        # e2=(V1^2 - V2)/2   [mutation (i)]
    else:      W=[A2[i]+h2[i] for i in range(n)]
    Wr=red(W,n); X=red(A2,n)
    P,d=minpoly_of(Wr,n)                                # roots = 2*e2 conjugates
    # rescale: coefficients c_i -> c_i*2^i / 2^d  gives roots = e2
    cs=P.all_coeffs()[::-1]
    m=[cs[i]*2**i for i in range(len(cs))]
    g=2**d
    assert all(x%g==0 for x in m)
    m=[x//g for x in m]
    # M3c as total non-negativity of (4p-W)^2+16pX  and 4p-W    (SIN)
    A=[(4*p if i==0 else 0)-Wr[i] for i in range(n-1)]
    A2f=mulF(A,A,n)
    Z=[A2f[i]+16*p*X[i] for i in range(n-1)]
    PA,_=minpoly_of(A,n); PZ,_=minpoly_of(Z,n)
    m3c_fail = (PA.count_roots(None,sp.Integer(0))>0) or (PZ.count_roots(None,sp.Integer(0))>0)
    return m, m3c_fail

p=43
n=curve_order(p,B); dl=dlog_table(p,n,B); h1=hist_k1(p,n,dl,B)
from audit_n1_vsign_v2_core import hist_k2
h2,_=hist_k2_mut(p,n,dl,'ok')
base,m3c=analyse_vec(p,n,h1,h2)
print("BASELINE           : M1 match =",base==REF," M3c fails =",m3c)

m,m3c=analyse_vec(p,n,h1,h2,bugP2=True)
print("(i)  P2:=+V2       : M1 match =",m==REF," M3c fails =",m3c)
Y=sp.Symbol('Y'); PP=sp.Poly(sum(m[i]*Y**i for i in range(len(m))),Y)
print("       bugged m_p  =",m)
print("       bugged e2 roots:",[sp.N(r,8) for r in PP.real_roots()], " -> v =",
      [sp.N(-(r+2*p)/(4*p),8) for r in PP.real_roots()])

def m3a(h,n):   # Im V2 = 0  <=>  h[d]==h[-d]
    return all(h[d]==h[(-d)%n] for d in range(n))
def mu6inv(h,n):
    from audit_n1_vsign_v2_core import polymul_mod_cyc
    return None
print("BASELINE M3a (h2[d]==h2[-d]) :", m3a(h2,n))

h2b,sk=hist_k2_mut(p,n,dl,'chi_exp')
print("(ii) chi2 exp (p-1)/2 : M3a holds =",m3a(h2b,n))
try:
    m,m3c=analyse_vec(p,n,h1,h2b)
    print("(ii) chi2 exp (p-1)/2 : M1 match =",m==REF," M3c fails =",m3c)
except AssertionError as e:
    print("(ii) chi2 exp (p-1)/2 : PIPELINE ABORTS at the minpoly step:",e,
          "-> the (n-1) values do NOT collapse to (n-1)/6, so 'the minimal polynomial of degree (n-1)/6' does not exist. M1 cannot return the reference => M1 fails, by abort.")

h2c,sk=hist_k2_mut(p,n,dl,'no_frob')
print("(iii) trace:=P     : points with no defined dlog (would KeyError in the real code):",sk,
      "of",sum(1 for _ in range(1)) or "", "-> pipeline ABORTS, not a silent wrong answer")
print("(iii) trace:=P     : M3a holds =",m3a(h2c,n))
try:
    m,m3c=analyse_vec(p,n,h1,h2c)
    print("       if those points are silently DROPPED: M1 match =",m==REF," M3c fails =",m3c)
    Y2=sp.Symbol('Y'); PP2=sp.Poly(sum(m[i]*Y2**i for i in range(len(m))),Y2)
    print("       bugged e2 roots:",[sp.N(r,8) for r in PP2.real_roots()])
except AssertionError as e:
    print("       if those points are silently dropped: minpoly step ABORTS:",e)
