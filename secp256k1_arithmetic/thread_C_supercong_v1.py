#!/usr/bin/env python3
"""
Thread C (2026-07-11): closed form of the mod-l^2 supercongruence correction
for  b_l = 7^{(l-1)/6} * C((l-1)/2, (l-1)/6)  vs the Hecke eigenvalue a_l,
at split primes l = 6k+1.

Known (v2): b_l = a_l (mod l).  Refinement target: b_l mod l^2.

For a CM curve the sharp statement is a Gauss/Jacobi-sum supercongruence.
Write the split prime  4l = L^2 + 27 M^2  (L = a_l up to sign, the trace;
M >= 1).  The classical CM supercongruence family (Beukers/Coster-van Hamme/
Z.-W. Sun type) predicts a relation of the shape

    b_l  ==  a_l  -  (l / a_l) * S_l   (mod l^2)

i.e. delta_l := (b_l - a_l)/l  (mod l), and we test whether delta_l is an
explicit function of the CM data (a_l, M, l) rather than Fermat quotients.

Candidate closed forms tested (exact, mod l), on ALL split l < 4000:
  C1: delta_l == c * (l - a_l^2)/a_l                        [trace-square]
  C2: delta_l == c * M * a_l^{-1}                           [conductor M]
  C3: b_l^2 == a_l^2 - 2l (mod l^2)  <=> b_l == +-sqrt(a^2-2l)  [norm form!]
  C4: Jacobi: b_l == a_l - l * (E_{l-2} type) ... approximated by
      b_l == a_l * (1 + l * H) with H a harmonic-ish sum -> test H = q-free
  C5: the ASD unit-root refinement:  b_l == alpha_l (mod l^2), where
      alpha_l = (a_l + sqrt(a_l^2 - 4l))/2 lifted 2-adically? (unit root)
The decisive candidate is C3/C5: the formal-group/Hasse relation forces
b_l to be the UNIT ROOT of X^2 - a_l X + l (mod l^2), i.e. b_l == alpha_l.
"""
import math
from fractions import Fraction

def sieve(L):
    bs=bytearray([1])*(L+1); bs[0:2]=b'\x00\x00'
    for i in range(2,math.isqrt(L)+1):
        if bs[i]: bs[i*i::i]=bytearray(len(bs[i*i::i]))
    return bs
def a_count(l):
    qr=bytearray(l)
    for x in range((l//2)+1): qr[x*x%l]=1
    c=1
    for x in range(l):
        v=(x*x*x+7)%l
        if v==0: c+=1
        elif qr[v]: c+=2
    return l+1-c
def b_(l): return 7**((l-1)//6)*math.comb((l-1)//2,(l-1)//6)

isp=sieve(4000)
splits=[l for l in range(13,4000) if isp[l] and l%3==1 and l!=7]

# --- C5: unit-root hypothesis  b_l == alpha_l (mod l^2) ----------------------
# alpha_l = the root of X^2 - a_l X + l that is a UNIT mod l (i.e. != 0 mod l).
# Hensel-lift from alpha_0 = a_l (mod l): alpha = a_l - l/a_l (mod l^2).
def unit_root_mod_l2(a,l):
    # X^2 - aX + l = 0 ; root near a: X = a - l*a^{-1} - ... solve mod l^2
    # let X = a + l*t ; (a+lt)^2 - a(a+lt) + l = 0 mod l^2
    #  a^2 + 2alt - a^2 - alt + l = 0 => a l t + l = 0 (mod l^2) => a t + 1 = 0 mod l
    #  t = -a^{-1} mod l
    t=(-pow(a%l,-1,l))%l
    return (a + l*t) % (l*l)

res={'C5_unitroot':0}
fails=[]
for l in splits:
    a=a_count(l); B=b_(l)%(l*l)
    ar=unit_root_mod_l2(a,l)
    if B==ar: res['C5_unitroot']+=1
    else: fails.append((l,a,B,ar))
print(f"C5  b_l == unit root of X^2-a_l X + l (mod l^2): "
      f"{res['C5_unitroot']}/{len(splits)}"
      + ("" if not fails else f"   first fails {fails[:3]}"))

# --- If C5 holds, then b_l^2 == a_l b_l - l (mod l^2), the ASD relation ------
c_asd=sum(1 for l in splits if (b_(l)**2 - a_count(l)*b_(l) + l) % (l*l)==0)
print(f"    equiv  b_l^2 - a_l b_l + l == 0 (mod l^2): {c_asd}/{len(splits)}")

# --- push to mod l^3: which primes upgrade? ----------------------------------
up=[l for l in splits if (b_(l)**2 - a_count(l)*b_(l) + l) % (l**3)==0]
print(f"    mod l^3 upgrades: {up}")
# characterize: relate to M in 4l=a^2+27M^2, and to a_l mod l
def LM(l):
    a=a_count(l); d=4*l-a*a
    assert d%27==0
    M2=d//27; M=math.isqrt(M2)
    return a,M
print("    upgrade data (l, a_l, M, a_l mod 3, l mod ...):")
for l in up:
    a,M=LM(l)
    print(f"      l={l}: a={a}, M={M}, M mod l = {M%l}, "
          f"3M == +-a? {3*M%l in (a%l,(-a)%l)}, a≡{a%9} mod9")

# --- second-order term: delta_l = (b_l - alpha_l)/l^2 mod l  (should be 0 by C5)
# instead extract the l^2->l^3 obstruction  eps_l := (b^2 - a b + l)/l^2 mod l
print("\n  l^2->l^3 obstruction  eps_l := (b_l^2 - a_l b_l + l)/l^2  (mod l):")
rows=[]
for l in splits[:20]:
    a=a_count(l); val=b_(l)**2 - a*b_(l) + l
    eps=(val//(l*l))%l
    a_,M=LM(l)
    rows.append((l,eps,a_%l,M%l))
    print(f"    l={l:4d}: eps={eps:4d}   a={a_%l:4d}  M mod l={M%l:4d}  "
          f"eps*a mod l={eps*a_%l:4d}")
