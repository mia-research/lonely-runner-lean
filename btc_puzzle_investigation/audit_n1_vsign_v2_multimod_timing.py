#!/usr/bin/env python3
"""Cost of the multi-modular minimal-polynomial step alone, at the real (n,p) of the
sweep.  W is synthetic but mu6-coset-constant with entries of the true size --
the cost of the algorithm depends on (n,d,p), not on W's values."""
import sys,time,random
sys.path.insert(0,"/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from audit_n1_vsign_v2_multimod import minpoly_multimodular, primitive_root
random.seed(7)
print(f"{'p':>6} {'n':>6} {'d':>5} {'multimod_s':>12} {'moduli':>7} {'bits':>7}")
for p,n in [(547,547),(1669,1663),(2503,2557),(3931,4021),(4513,4597),(6007,6163)]:
    d=(n-1)//6
    g=primitive_root(n); mu=[pow(g,k*d,n) for k in range(6)]
    W=[0]*n
    W[0]=random.randint(-6*p,6*p)
    for j in range(d):
        r=pow(g,j,n); val=random.randint(-2*p,2*p)
        for m in mu: W[r*m%n]=val
    t0=time.time()
    c=minpoly_multimodular(n,W,p)
    t=time.time()-t0
    from audit_n1_vsign_v2_multimod import is_prime
    nq=0; prod=1; bound=(1+6*p)**d
    print(f"{p:>6} {n:>6} {d:>5} {t:>12.2f} {'':>7} {max(abs(x).bit_length() for x in c):>7}", flush=True)
