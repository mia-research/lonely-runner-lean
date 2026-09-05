#!/usr/bin/env python3
"""MEASURED cost of the ADDITION's three stages.  Stage A = e2(1) as an exact
integer vector (the spec's 'O(n^2) per prime').  Stage B = minimal polynomial in
Z[Y].  Stage C = Sturm on the shifted polynomial."""
import sys, time, json
sys.path.insert(0,"/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from audit_n1_vsign_v2_core import compute_e2_poly, is_prime, curve_order
from audit_n1_vsign_v2_minpoly import analyse
import sympy as sp

PRIMES=[int(x) for x in sys.argv[1].split(",")]
res={}
for p in PRIMES:
    t0=time.time(); n,h1,h2,W = compute_e2_poly(p); tA=time.time()-t0
    d=(n-1)//6
    t0=time.time(); r=analyse(p); tB=time.time()-t0
    c=r['minpoly']
    bits=max(x.bit_length() for x in c)
    Y=sp.Symbol('Y')
    m=sum(c[i]*Y**i for i in range(len(c)))
    P=sp.Poly(m,Y)
    two_p = 2*p
    t0=time.time()
    if p%4==3:  cnt=P.count_roots(None, sp.Integer(-two_p))    # roots below -2p
    else:       cnt=P.count_roots(sp.Integer(two_p), None)     # roots above +2p
    tC=time.time()-t0
    t0=time.time(); nreal=len(P.real_roots()); tRR=time.time()-t0
    res[p]=dict(n=n,d=d,tA=tA,tB=tB,tC=tC,tRR=tRR,maxbits=bits,bad=int(cnt),nreal=nreal,
                totally_real=(nreal==d))
    print(f"p={p:5d} n={n:5d} d={d:4d} | A {tA:8.2f}s  B {tB:9.2f}s  C(Sturm) {tC:7.2f}s"
          f"  realroots {tRR:7.2f}s | maxcoefbits {bits:6d} | totally_real={nreal==d}"
          f" | #classes on wrong side = {cnt}", flush=True)
json.dump(res, open("audit_n1_vsign_v2_timing_%s.json"%PRIMES[-1],"w"), indent=1)
