#!/usr/bin/env python3
"""MEASURED cost of the ADDITION's Sturm step alone, on synthetic totally-real
integer polynomials of the size the sweep actually produces.
m_p(Y) = prod (Y - r_i), r_i integers in [-6p, 6p], degree d = (n-1)/6."""
import time, random, sys
import sympy as sp
random.seed(1)
Y=sp.Symbol('Y')
print(f"{'d':>5} {'p':>6} {'maxbits':>8} {'build_s':>9} {'shift_s':>9} {'sturm_s':>10} {'descartes_s':>12}")
for d,p in [(20,127),(50,349),(100,733),(150,907),(200,1237),(300,1831),(400,2503)]:
    B=6*p
    roots=[random.randint(-B,B) for _ in range(d)]
    t0=time.time()
    c=[1]
    for r in roots:
        c=[0]+c
        for i in range(len(c)-1): c[i]-= r*c[i+1]
    tb=time.time()-t0
    bits=max(abs(x).bit_length() for x in c)
    P=sp.Poly(list(reversed(c)),Y)
    # Taylor shift X -> X - 2p  (integer arithmetic, Horner/synthetic division)
    t0=time.time()
    sh=list(c)
    a=-2*p
    for k in range(d):
        for i in range(d-1,k-1,-1):
            sh[i]+=a*sh[i+1]
    tsh=time.time()-t0
    t0=time.time()
    try:
        cnt=P.count_roots(None,sp.Integer(-2*p)); ts=time.time()-t0
    except Exception as e:
        ts=float('nan'); cnt='ERR'
    t0=time.time()
    sgn=[1 if x>0 else (-1 if x<0 else 0) for x in sh]
    ch=0; prev=0
    for s in sgn:
        if s==0: continue
        if prev!=0 and s!=prev: ch+=1
        prev=s
    td=time.time()-t0
    print(f"{d:>5} {p:>6} {bits:>8} {tb:>9.2f} {tsh:>9.3f} {ts:>10.2f} {td:>12.5f}   sturm_cnt={cnt} descartes_signchanges_of_g(-X)= (see note)", flush=True)
