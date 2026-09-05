#!/usr/bin/env python3
"""Multi-modular EXACT minimal polynomial of e2(1) -- the algorithm the ADDITION
needs but does not name.  All arithmetic is modular integer arithmetic + CRT:
exact, zero floats.

Key structure used: e2(1) is mu6-invariant, so its coefficient vector is constant
on mu6-cosets, i.e. e2 = (w0 + sum_j c_j eta_j)/2 with eta_j the Gaussian periods
of degree d=(n-1)/6.  The d conjugates are then a CYCLIC CORRELATION of (c_j) with
(eta_j), computable in O(d^2) per modulus instead of O(n^2)."""
import sys, time, random
sys.path.insert(0,"/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation")
from audit_n1_vsign_v2_core import compute_e2_poly, is_prime

def primitive_root(n):
    fac=set(); m=n-1; dd=2
    while dd*dd<=m:
        while m%dd==0: fac.add(dd); m//=dd
        dd+=1
    if m>1: fac.add(m)
    g=2
    while True:
        if all(pow(g,(n-1)//f,n)!=1 for f in fac): return g
        g+=1

def minpoly_multimodular(n, W, p, verbose=False):
    d=(n-1)//6
    g=primitive_root(n)
    mu=[pow(g,k*d,n) for k in range(6)]
    reps=[pow(g,j,n) for j in range(d)]
    c=[]
    for j,r in enumerate(reps):
        vals={W[r*m%n] for m in mu}
        assert len(vals)==1, "W not constant on mu6 coset -> e2 not mu6-invariant"
        c.append(W[r])
    w0=W[0]
    # coefficient bound of prod (Y - e2_i):  |e2_i| <= 6p
    bound=1
    for _ in range(d): bound*= (1+6*p)
    need=2*bound
    # moduli q = 1 mod n, ~2^61
    qs=[]; prod=1; q=(1<<61)//n*n+1
    while prod<need:
        if is_prime(q): qs.append(q); prod*=q
        q+=n
    if verbose: print(f"    d={d} moduli={len(qs)} bound_bits={bound.bit_length()}")
    residues=[]
    for q in qs:
        # primitive n-th root of unity mod q
        while True:
            h=random.randrange(2,q)
            w=pow(h,(q-1)//n,q)
            if w!=1: break
        wp=[0]*n; t=1
        for i in range(n): wp[i]=t; t=t*w%q
        eta=[sum(wp[r*m%n] for m in mu)%q for r in reps]
        inv2=pow(2,q-2,q)
        val=[ (w0+sum(c[j]*eta[(i+j)%d] for j in range(d)))*inv2 % q for i in range(d)]
        # product of linear factors mod q
        poly=[1]
        for v in val:
            poly=[0]+poly
            nv=(-v)%q
            for i in range(len(poly)-1): poly[i]=(poly[i]+nv*poly[i+1])%q
        residues.append(poly)
    # CRT, symmetric range
    M=1
    for q in qs: M*=q
    coeffs=[]
    Minv=[ (M//q, pow((M//q)%q, q-2, q)) for q in qs ]
    for i in range(d+1):
        x=0
        for (Mi,mi),poly,q in zip(Minv,residues,qs):
            x=(x+poly[i]*Mi%M*mi)%M
        if x> M//2: x-=M
        coeffs.append(x)
    return coeffs   # low -> high

if __name__=="__main__":
    for p in [int(x) for x in sys.argv[1].split(',')]:
        t0=time.time(); n,h1,h2,W=compute_e2_poly(p); tA=time.time()-t0
        t0=time.time(); c=minpoly_multimodular(n,W,p,verbose=True); tB=time.time()-t0
        print(f"p={p:6d} n={n:5d} d={(n-1)//6:5d} | stageA {tA:8.2f}s | stageB(multimod) {tB:9.2f}s"
              f" | maxbits {max(abs(x).bit_length() for x in c)}", flush=True)
        if p in (13,43,127):
            print("   m_p low->high:",c)
