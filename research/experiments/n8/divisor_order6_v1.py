"""Divisor-closed: convert the order-6 real witness into an integer one.
Clear at modulus b:  q mod b in [L,U],  L = ceil((b-1)/8), U = floor((7b-1)/8).
In fractional terms x = (q mod b)/b, the clear window is [1/8 - 1/(8b), 7/8 - 1/(8b)].

Order-6 LRC (in-house intLRC_six) gives a REAL t with dist(t/b_i, Z) >= 1/6 for all i.
Round to the nearest integer q: |q-t| <= 1/2, so x_i moves by at most 1/(2b_i).
  left  : 1/6 - 1/(2b) >= 1/8 - 1/(8b)  <=>  1/24 >= 3/(8b)  <=>  b >= 9
  right : 5/6 + 1/(2b) <= 7/8 - 1/(8b)  <=>  1/24 >= 5/(8b)  <=>  b >= 15
So rounding is valid once every b_i >= 15.  Test the arithmetic, then find the TRUE threshold."""
from math import gcd, lcm
from fractions import Fraction as F
import random, itertools
def L(b): return -((-(b-1))//8)          # ceil((b-1)/8)
def U(b): return (7*b-1)//8
def clear(q,b): return L(b) <= q % b <= U(b)
def exists_q(bs):
    M=lcm(*bs)
    return any(all(clear(q,b) for b in bs) for q in range(M))
print("(1) window arithmetic: is [1/6,5/6] shifted by 1/(2b) inside [1/8-1/(8b), 7/8-1/(8b)]?")
for b in range(2,20):
    lo_ok = F(1,6)-F(1,2*b) >= F(1,8)-F(1,8*b)
    hi_ok = F(5,6)+F(1,2*b) <= F(7,8)-F(1,8*b)
    print(f"   b={b:2d}: left {'ok ' if lo_ok else 'NO '} right {'ok ' if hi_ok else 'NO '}"
          f"{'  <-- both hold' if lo_ok and hi_ok else ''}")
print("\n(2) does an integer q exist, as a function of the SMALLEST modulus?")
random.seed(1)
for B in range(2,17):
    bad=0; n=0
    for _ in range(3000):
        bs=[random.randint(B,B+14) for _ in range(5)]
        if lcm(*bs)>4_000_000: continue
        n+=1
        if not exists_q(bs): bad+=1
    print(f"   min modulus >= {B:2d}: {n-bad}/{n} admit an integer q"
          f"{'   (none fail)' if bad==0 else f'   {bad} FAIL'}")
print("\n(3) smallest 5-tuple with NO integer q (exhaustive over small moduli):")
found=None
for hi in range(2,13):
    for bs in itertools.combinations_with_replacement(range(2,hi+1),5):
        if max(bs)!=hi: continue
        if lcm(*bs)<=2_000_000 and not exists_q(bs): found=bs; break
    if found: break
print(f"   {found}  (L,U per modulus: {[(b,L(b),U(b)) for b in found] if found else '-'})")
