#!/usr/bin/env python3
"""
Settle thread B: does our amicable-closure census reproduce Silverman-Stange
Conjecture 40 (arXiv:0912.1831) for the j=0 family y^2 = x^3 + k?

Their definitions (paper Section 6/7):
  N_k(X)     = #{ p < X : #E_p(F_p) is prime }
  N_k^[1](X) = #{ Type-1 primes < X }
  Q_k(X)     = #{ amicable pairs (p,q), p<q, p<=X }
  Conjecture 40:  N_k^[1](X) ~ (1/3 + R(k)) N_k(X),  R(k) by k mod 36 (table).
  Conjecture 27:  Q_k(X)     ~ (1/4) N_k^[1](X).

OUR quantity (convention-free, directly measurable):
  rho_k = P( #E(F_q) = ell | q := #E(F_ell) is prime )
        = [# primes ell<X, #E_ell prime, that close] / [# primes ell<X, #E_ell prime]
        = 2 Q_k(X) / N_k(X)                      (each amicable pair has 2 members)
        ~ 2 * (1/4) * (1/3 + R(k))
        = (1/2)(1/3 + R(k)).                     <-- the S-S prediction for rho_k

Test: measure rho_k directly (exact point-count-based a_ell via the validated
sextic-symbol formula, cross-checked vs brute) for k in {5,7,11,13,17,19,23,
29,31,37} and compare to (1/2)(1/3 + R(k)).  A match across all k SETTLES B:
our 13/50 for secp256k1's k=7 is exactly the S-S conjectural value -- a
reconstruction/validation, not a new theorem.
"""

import math
from fractions import Fraction

UNITS=[(1,0),(-1,0),(0,1),(0,-1),(-1,-1),(1,1)]
IDX2POW={0:0,1:3,2:2,3:5,4:4,5:1}; POW2IDX={v:k for k,v in IDX2POW.items()}
def mulw(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]-a[1]*b[1])
def Tr(v): return 2*v[0]-v[1]
def conj(v): return (v[0]-v[1],-v[1])
def primary(v):
    for i,u in enumerate(UNITS):
        w=mulw(u,v)
        if w[0]%3==2 and w[1]%3==0: return w
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
def a_count(ell,k):
    qr=bytearray(ell)
    for x in range((ell//2)+1): qr[x*x%ell]=1
    c=1
    for x in range(ell):
        v=(x*x*x+k)%ell
        if v==0: c+=1
        elif qr[v]: c+=2
    return ell+1-c
def u_b(ell,pip,k):
    pc=conj(pip); w=(-pc[0]*pow(pc[1],-1,ell))%ell
    tab={(u[0]+u[1]*w)%ell:i for i,u in enumerate(UNITS)}
    c=(4*k)%ell
    if c==0: return None
    s=pow(c,(ell-1)//6,ell)
    if s not in tab: return None
    return POW2IDX[(IDX2POW[tab[s]]+3)%6]
def a_fast(ell,k):
    pip=primary(cornacchia(ell))
    u=u_b(ell,pip,k)
    if u is None: return None
    return Tr(mulw(UNITS[u],pip))

def R_ss(k):
    r=k%36
    if r in (1,19):  return Fraction(2,3*(k-3))
    if r in (17,35): return Fraction(2,3*(k-1))
    if r in (13,25): return Fraction(0)
    if r in (5,29):  return Fraction(0)
    if r in (7,31):  return Fraction(2*k,3*(k-2)**2)
    if r in (11,23): return Fraction(2*k,3*(k*k-2))
    return None
def rho_pred(k): return Fraction(1,2)*(Fraction(1,3)+R_ss(k))

X=600_000
isp=sieve(X)
splitprimes=[ell for ell in range(11,X) if isp[ell] and ell%3==1]
print(f"X = {X}, split primes ell<X: {len(splitprimes)}\n")

# validate a_fast vs brute on a sample per k
print("k  | val a_fast (30 primes) | rho_direct  measured | S-S (1/2)(1/3+R(k))  | ratio")
print("-"*88)
import random
random.seed(7)
for k in (5,7,11,13,17,19,23,29,31,37):
    # validate formula
    samp=random.sample([e for e in splitprimes if e<8000 and e%k!=0],25)
    okv=all(a_fast(e,k)==a_count(e,k) for e in samp)
    tot=cl=0
    for ell in splitprimes:
        if ell%k==0: continue
        aL=a_fast(ell,k)
        if aL is None: continue
        q=ell+1-aL
        if q<=7 or q%3!=1 or q%k==0: continue
        # q prime?
        if q<X:
            if not isp[q]: continue
        else:
            # Miller-Rabin
            m=q; d0=m-1; s0=0
            while d0%2==0: d0//=2; s0+=1
            prime=True
            for a0 in (2,3,5,7,11,13,17,19,23,29,31,37):
                if a0%m==0: continue
                xx=pow(a0,d0,m);
                if xx in (1,m-1): continue
                for _ in range(s0-1):
                    xx=xx*xx%m
                    if xx==m-1: break
                else: prime=False; break
            if not prime: continue
        aQ=a_fast(q,k)
        if aQ is None: continue
        tot+=1
        if aQ==2-aL: cl+=1
    meas=cl/tot
    pred=float(rho_pred(k))
    print(f"{k:2d} | {'OK' if okv else 'BAD':>3}  n={tot:5d}          | {meas:.5f}            "
          f"| {str(rho_pred(k)):>10} = {pred:.5f} | {meas/pred:.3f}")

print("\nInterpretation: ratio ~ 1.00 across all k  =>  our rho_k reproduces")
print("Silverman-Stange Conjecture 40 (+ Conj 27); 13/50 for k=7 is their value.")
