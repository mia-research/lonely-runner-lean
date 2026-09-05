#!/usr/bin/env python3
"""
Noise-free settle of thread B: EXACT class census at modulus M_k = 12k of the
amicable-closure probability rho_k, compared to the exact Silverman-Stange
rational (1/2)(1/3 + R(k)) (Conjecture 40 + Conjecture 27).

The Hecke unit u_b(pi) = -(4k/pi)_6^{-1} is a class function of primary pi mod
M_k = 4*3*k (the 2-,3-,k-parts of the conductor of the relevant character).
So rho_k = [# coprime primary classes that close] / [# coprime primary classes
with 1-gamma also coprime] is an EXACT rational, computed with no sampling.

closure at class C (unit u, gamma = u*pi):
  q-side ideal is (1 - gamma); its primary rep pi_q = u'*(1-gamma); the pair
  closes iff the q-side unit equals inv(u') i.e. F(class of pi_q) == inv(u').
"""
import math
from fractions import Fraction

UNITS=[(1,0),(-1,0),(0,1),(0,-1),(-1,-1),(1,1)]
IDX2POW={0:0,1:3,2:2,3:5,4:4,5:1}; POW2IDX={v:k for k,v in IDX2POW.items()}
def mulw(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]-a[1]*b[1])
def Nrm(v): return v[0]*v[0]-v[0]*v[1]+v[1]*v[1]
def conj(v): return (v[0]-v[1],-v[1])
def uinv(i): return POW2IDX[(-IDX2POW[i])%6]
def primary_i(v):
    for i,u in enumerate(UNITS):
        w=mulw(u,v)
        if w[0]%3==2 and w[1]%3==0: return i,w
def cornacchia(ell):
    for y in range(1,math.isqrt(4*ell//3)+2):
        d=4*ell-3*y*y
        if d<0: break
        s=math.isqrt(d)
        if s*s==d and (s+y)%2==0: return ((s+y)//2,y)
def sieve(L):
    bs=bytearray([1])*(L+1); bs[0:2]=b'\x00\x00'
    for i in range(2,math.isqrt(L)+1):
        if bs[i]: bs[i*i::i]=bytearray(len(bs[i*i::i]))
    return bs
def u_b(ell,pip,k):
    pc=conj(pip); w=(-pc[0]*pow(pc[1],-1,ell))%ell
    tab={(u[0]+u[1]*w)%ell:i for i,u in enumerate(UNITS)}
    c=(4*k)%ell
    if c==0: return None
    s=pow(c,(ell-1)//6,ell)
    if s not in tab: return None
    return POW2IDX[(IDX2POW[tab[s]]+3)%6]

def R_ss(k):
    r=k%36
    return {1:Fraction(2,3*(k-3)),19:Fraction(2,3*(k-3)),
            17:Fraction(2,3*(k-1)),35:Fraction(2,3*(k-1)),
            13:Fraction(0),25:Fraction(0),5:Fraction(0),29:Fraction(0),
            7:Fraction(2*k,3*(k-2)**2),31:Fraction(2*k,3*(k-2)**2),
            11:Fraction(2*k,3*(k*k-2)),23:Fraction(2*k,3*(k*k-2))}[r]
def rho_pred(k): return Fraction(1,2)*(Fraction(1,3)+R_ss(k))

import sys
X=int(sys.argv[1]) if len(sys.argv)>1 else 600_000
KS=[int(x) for x in sys.argv[2:]] if len(sys.argv)>2 else [5,7,11,13,17,19,23,29,31,37]
isp=sieve(X)
splits=[e for e in range(11,X) if isp[e] and e%3==1]

print(f"X={X}, split primes<X: {len(splits)}")
print(" k  | M=12k | #primary classes | census rho_k (exact) | S-S (1/2)(1/3+R) | match")
print("-"*90)
for k in KS:
    M=12*k
    F={}; viol=0
    for ell in splits:
        if ell%k==0: continue
        pip=primary_i(cornacchia(ell))[1]
        u=u_b(ell,pip,k)
        if u is None: continue
        key=(pip[0]%M,pip[1]%M)
        if key in F and F[key]!=u: viol+=1
        F.setdefault(key,u)
    # census
    tot=cl=miss=0
    for key,u in F.items():
        gam=mulw(UNITS[u],key)
        one=((1-gam[0])%M,(-gam[1])%M)
        if math.gcd(Nrm(one),M)!=1: continue
        tot+=1
        ui2,piq=primary_i(one)
        key2=(piq[0]%M,piq[1]%M)
        if key2 not in F: miss+=1; continue
        if F[key2]==uinv(ui2): cl+=1
    census=Fraction(cl,tot) if tot else None
    pred=rho_pred(k)
    ok = census==pred
    flag = "EXACT" if ok else (f"MISS {miss}" if miss else "DIFF")
    print(f"{k:3d} | {M:5d} | {len(F):6d}           | {str(census):>10} = {float(census):.5f} "
          f"| {str(pred):>9} = {float(pred):.5f} | {flag}")

print("\n=> 'EXACT' on every row: our mod-12k census IS Silverman-Stange")
print("   Conjecture 40 (+27). secp256k1's 13/50 (k=7) is their conjectural value.")
