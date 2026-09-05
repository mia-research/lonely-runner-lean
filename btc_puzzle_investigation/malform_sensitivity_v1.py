#!/usr/bin/env python3
"""
Malformation / perturbation probe: deliberately perturb or MALFORM the construction
and trace the effect into the point (X,Y) and the decomposition (n,k,D). Maps the
pipeline's sensitivity structure: the CURVE map should be an avalanche (locality
destroyed = DLP mixing), the DECOMPOSITION should be piecewise-continuous (locality
preserved within a Farey cell, jumps at boundaries). Malformed (n,k,D) inputs show
whether the construction is consistent/invertible and how it fails.
Exact integers only.
"""
import random
from fractions import Fraction
p=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Gx=0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy=0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
def inv(a):return pow(a,p-2,p)
def padd(P,Q):
    if P is None:return Q
    if Q is None:return P
    x1,y1=P;x2,y2=Q
    if x1==x2 and (y1+y2)%p==0:return None
    s=((3*x1*x1)*inv(2*y1) if P==Q else (y2-y1)*inv((x2-x1)%p))%p
    x3=(s*s-x1-x2)%p;return(x3,(s*(x1-x3)-y1)%p)
def mul(k):
    R=None;P=(Gx,Gy)
    while k:
        if k&1:R=padd(R,P)
        P=padd(P,P);k>>=1
    return R
def hdist(u,v): return bin((u^v)&((1<<256)-1)).count('1')
def decomp(d,b):
    A=1<<(b-1); fr=Fraction(d-A,A).limit_denominator(256); n,k=fr.denominator,fr.numerator
    D=d-A-(A*k)//n
    return n,k,D
def build(n,k,D,b):
    A=1<<(b-1); return A+(A*k)//n+D

b=64; A=1<<(b-1); rng=random.Random(7)
d0=A+rng.randrange(A)
X0,Y0=mul(d0); n0,k0,D0=decomp(d0,b)
print(f"base d0 ({b}-bit): (n,k,D)=({n0},{k0},{D0})")

print("\n=== 1. AVALANCHE: perturb d0 by delta -> bit-change in (X,Y); change in (n,k,D) ===")
print(f"{'delta':>7}{'ΔX bits':>9}{'ΔY bits':>9}   (n,k,D)")
for delta in [1,2,3,7,16,257,10**6,10**12]:
    d=d0+delta; X,Y=mul(d); n,k,D=decomp(d,b)
    print(f"{delta:>7}{hdist(X,X0):>9}{hdist(Y,Y0):>9}   ({n},{k},{D})  Δn={n-n0} Δk={k-k0} ΔD={D-D0}")
# bit-flips
print("  single-bit flips of d0:")
for bit in [0,10,30,62]:
    d=d0^(1<<bit); X,Y=mul(d); n,k,D=decomp(d,b)
    print(f"   flip bit {bit:2d}: ΔX={hdist(X,X0):3d} ΔY={hdist(Y,Y0):3d} bits; (n,k,D)=({n},{k},{D})")

print("\n=== 2. cell stability: how far can d0 move before the (n,k) Farey cell changes? ===")
def far(step):  # binary-search largest offset in +/- direction keeping the (n,k) cell
    lo,hi=0,1
    while decomp(d0+step*hi,b)[:2]==(n0,k0): hi*=2
    while hi-lo>1:
        mid=(lo+hi)//2
        if decomp(d0+step*mid,b)[:2]==(n0,k0): lo=mid
        else: hi=mid
    return lo
lo=far(-1); hi=far(1); width=lo+hi+1
print(f"  (n,k)=({n0},{k0}) stable for d in [d0-{lo}, d0+{hi}]  => cell width ~{width}")
print(f"  cell width vs A/n^2 estimate: {width} vs {A//(n0*n0)}")

print("\n=== 3. MALFORMED (n,k,D) construction -> rebuild d -> re-decompose + point ===")
cases=[
 ("normal",           n0,k0,D0),
 ("non-coprime 2n,2k", 2*n0,2*k0,D0),
 ("D negative",       n0,k0,-abs(D0)-5),
 ("D overflow +cell",  n0,k0,D0+(lo+hi+1)),
 ("k>n (>1 ratio)",    n0,n0+k0,D0),
]
for name,n,k,D in cases:
    d=build(n,k,D,b)
    if not (1<=d): print(f"  {name:18}: d nonpositive ({d})"); continue
    nn,kk,DD=decomp(d,b); X,Y=mul(d)
    same = (nn,kk)==(n0,k0)
    print(f"  {name:18}: built d -> re-decomp (n,k,D)=({nn},{kk},{DD})  point X≡{X%(1<<16):5d}(low16)  {'SAME cell' if same else 'MOVED cell'}")
print("\nreading: curve map = avalanche (any delta -> ~half X,Y bits flip => no locality"
      "\n leaks the DLP); decomposition = piecewise-continuous (n,k fixed across a cell,"
      "\n D absorbs the perturbation) with hard jumps at cell walls; malformed (n,k,D)"
      "\n still yields a valid integer d whose canonical re-decomposition self-corrects.")
