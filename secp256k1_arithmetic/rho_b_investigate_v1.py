#!/usr/bin/env python3
"""
Continue-investigation (2026-07-11): the per-b amicable closure constant rho_b.

The 13/50 census for b=7 generalizes: for y^2 = x^3 + b (b squarefree-ish, the
six sextic twists), amicability closure ell -> #E_b(F_ell) -> ell is a class
condition on the primary Frobenius mod (conductor). Two internal cross-checks:

(1) rho_b via EXACT class census over primaries mod L_b (L_b = 4b or 12b), for
    b = 1,2,3,5,7.  This is unconditional arithmetic.
(2) The Silverman-Stange amicable DENSITY heuristic:
        A_b(X) ~ rho_b * C_HL(b) * X/(log X)^2 * (correction)
    Predicts the RATIO of pair-counts across b.  Round-37 measured (equal X):
    b=2 -> 24, b=3 -> 14, b=7 -> 19 pairs.  Test whether the census-based
    weights reproduce that ordering; a match is strong internal validation,
    a mismatch localizes the error.

Also directly recount amicable pairs for b=2,3,5,7 to X=20000 (point counts,
exact) so the comparison uses one consistent bound, not the relayed round-37.
"""

import math
from fractions import Fraction

UNITS = [(1,0), (-1,0), (0,1), (0,-1), (-1,-1), (1,1)]
IDX2POW = {0:0, 1:3, 2:2, 3:5, 4:4, 5:1}
POW2IDX = {v:k for k,v in IDX2POW.items()}
def mulw(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]-a[1]*b[1])
def Nrm(v): return v[0]*v[0]-v[0]*v[1]+v[1]*v[1]
def Tr(v): return 2*v[0]-v[1]
def conj(v): return (v[0]-v[1], -v[1])
def uinv(i): return POW2IDX[(-IDX2POW[i]) % 6]
def primary(v):
    hits=[(i,mulw(u,v)) for i,u in enumerate(UNITS)
          if (u[0]*v[0]-u[1]*v[1])%3==2 and (u[0]*v[1]+u[1]*v[0]-u[1]*v[1])%3==0]
    return hits[0]
def cornacchia(ell):
    for y in range(1, math.isqrt(4*ell//3)+2):
        d=4*ell-3*y*y
        if d<0: break
        s=math.isqrt(d)
        if s*s==d and (s+y)%2==0: return ((s+y)//2,y)
def sieve(L):
    bs=bytearray([1])*(L+1); bs[0:2]=b'\x00\x00'
    for i in range(2,math.isqrt(L)+1):
        if bs[i]: bs[i*i::i]=bytearray(len(bs[i*i::i]))
    return [i for i in range(L+1) if bs[i]]

def a_count(ell,b):
    qr=bytearray(ell)
    for x in range((ell//2)+1): qr[x*x%ell]=1
    cnt=1
    for x in range(ell):
        v=(x*x*x+b)%ell
        if v==0: cnt+=1
        elif qr[v]: cnt+=2
    return ell+1-cnt

# ------- unit character for general b:  u_b(pi) = -(4b/pi)_6^{-1} -------------
def u_b(ell, pip, b):
    pc=conj(pip); w=(-pc[0]*pow(pc[1],-1,ell))%ell
    tab={(u[0]+u[1]*w)%ell:i for i,u in enumerate(UNITS)}
    c=(4*b)%ell
    if c%ell==0: return None
    s=pow(c,(ell-1)//6,ell)
    if s not in tab: return None
    return POW2IDX[(IDX2POW[tab[s]]+3)%6]

primes=sieve(60000)
# validate u_b against brute a_count for each b on split primes < 3000
print("=== validate u_b = -(4b/pi)_6^{-1} against point counts ===")
for b in (1,2,3,5,7):
    bad=0; ok=0
    for ell in primes:
        if ell%3!=1 or ell<=7 or ell%abs(b)==0: continue
        if ell>3000: break
        pip=primary(cornacchia(ell))[1]
        u=u_b(ell,pip,b)
        if u is None: continue
        pred=Tr(mulw(UNITS[u],pip))
        if pred==a_count(ell,b): ok+=1
        else: bad+=1
    print(f"  b={b}: {ok} match, {bad} mismatch "
          f"{'(formula holds)' if bad==0 else '(FORMULA FAILS -- b-dependent sign?)'}")

# ------- exact rho_b census over classes mod 84 (works for all b coprime 84) --
print("\n=== exact closure fraction rho_b (class census mod 84) ===")
def coprime84(v): return math.gcd(Nrm(v),84)==1
rho={}
for b in (1,2,3,5,7):
    # build class map mod 84 from split primes
    F={}
    for ell in primes:
        if ell%3!=1 or ell<=7 or ell%abs(b)==0: continue
        pip=primary(cornacchia(ell))[1]
        u=u_b(ell,pip,b)
        if u is None: continue
        F[(pip[0]%84,pip[1]%84)]=u
    if len(F)<432:
        print(f"  b={b}: only {len(F)} classes seen; skip"); continue
    total=closing=0
    for key,u in F.items():
        gam=mulw(UNITS[u],key)
        q=((1-gam[0])%84,(-gam[1])%84)
        if not coprime84(q): continue
        total+=1
        ui2,piq=primary(q)
        key2=(piq[0]%84,piq[1]%84)
        if key2 in F and F[key2]==uinv(ui2): closing+=1
    rho[b]=Fraction(closing,total)
    print(f"  b={b}: {closing}/{total} = {rho[b]} = {float(rho[b]):.4f}")

# ------- direct recount of amicable pairs to common X=20000, all b -----------
print("\n=== direct amicable-pair recount to X=20000 (exact point counts) ===")
X=20000
psmall=[q for q in primes if q<=X]
pset=set(psmall)
counts={}
for b in (1,2,3,5,7):
    seen=set(); pairs=0
    for ell in psmall:
        if ell<=7 or ell%abs(b)==0: continue
        q=ell+1-a_count(ell,b)
        if q<=7 or q>X or q not in pset or q%abs(b)==0: continue
        back=q+1-a_count(q,b)
        if back==ell and ell<q:               # count each unordered pair once
            pairs+=1
    counts[b]=pairs
    print(f"  b={b}: {pairs} amicable pairs (unordered, both < {X})")

print("\n=== cross-check: does rho_b ordering track pair-count ordering? ===")
print("  round-37 relayed (equal X): b2=24, b3=14, b7=19")
print(f"  this run  X={X}:            " +
      ", ".join(f"b{b}={counts[b]}" for b in (2,3,5,7)))
print(f"  census rho_b:               " +
      ", ".join(f"b{b}={float(rho[b]):.3f}" for b in (2,3,5,7) if b in rho))
# HL-type prediction requires C_HL(b); the class fraction rho_b is only the
# local-alignment factor. Report both; interpretation in findings doc.
