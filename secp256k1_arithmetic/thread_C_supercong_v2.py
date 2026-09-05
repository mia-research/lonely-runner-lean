#!/usr/bin/env python3
"""
Thread C v2 (2026-07-11): the mod-l^2 structure of the formal-log numerators
  b_m = 7^{(m-1)/6} * C((m-1)/2, (m-1)/6)   (numerator of the T^m coeff)
against the Hecke eigenvalue a_l, at split primes l = 6k+1.

Correct objects (v1 conflated (b_l)^2 with b_{l^2}):
 (B) THREE-TERM ASD (Honda):  b_{l^2} - a_l b_l + l == 0 (mod l^2)   [the real one]
 (A) raw refinement: is b_l == a_l (mod l^2)?  delta_l := (b_l - a_l)/l mod l.
 (C) closed form hunt for delta_l using CM data (a_l, g_l where 4l = a_l^2+3 g_l^2).

All exact mod l^2 / l^3.
"""
import math

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
def b_(m): return 7**((m-1)//6)*math.comb((m-1)//2,(m-1)//6)
def gl(l,a):
    d=4*l-a*a
    assert d%3==0
    g2=d//3; g=math.isqrt(g2)
    assert g*g==g2
    return g

isp=sieve(2200)
splits=[l for l in range(13,2000) if isp[l] and l%3==1 and l!=7]
print(f"split primes 13..2000: {len(splits)}\n")

# (B) three-term ASD (the correct Honda relation) ----------------------------
c2=[l for l in splits if (b_(l*l)-a_count(l)*b_(l)+l)%(l*l)==0]
c3=[l for l in splits if (b_(l*l)-a_count(l)*b_(l)+l)%(l**3)==0]
print(f"(B) three-term  b_(l^2) - a_l b_l + l == 0 (mod l^2): {len(c2)}/{len(splits)} "
      f"{'ALL' if len(c2)==len(splits) else 'FAILS:'+str([x for x in splits if x not in c2][:5])}")
print(f"    upgrades to mod l^3 at: {c3}")

# (A) is b_l == a_l mod l^2 ? --------------------------------------------------
delta={}
zero=0
for l in splits:
    a=a_count(l); d=((b_(l)-a)//l)%l   # (b_l - a_l)/l is an integer since b==a mod l
    assert (b_(l)-a)%l==0
    delta[l]=d
    if d==0: zero+=1
print(f"\n(A) b_l == a_l (mod l): all ✓; of these, b_l == a_l (mod l^2) "
      f"(i.e. delta_l==0): {zero}/{len(splits)}")
print(f"    delta_l sample (l, a_l, g_l, delta_l): ", end="")
print([(l,a_count(l),gl(l,a_count(l)),delta[l]) for l in splits[:6]])

# (C) closed-form hunt for delta_l -------------------------------------------
# Candidates (mod l):  delta == c0 + c1*a + c2*a^{-1} + c3*g*a^{-1} + c4*l*a^{-1}...
# work in the invariant  D := delta_l * a_l (mod l)   [clears the a^{-1}]
def test(name, f):
    ok=all((delta[l]-f(l,a_count(l),gl(l,a_count(l))))%l==0 for l in splits)
    print(f"    [{'HIT' if ok else '   '}] {name}")
    return ok
inv=lambda a,l: pow(a%l,-1,l)
# harmonic-type H_l = sum_{j=1}^{(l-1)/6} 1/j (mod l): Lehmer-style
def H16(l):
    s=0
    for j in range(1,(l-1)//6+1): s=(s+inv(j,l))%l
    return s
def H12(l):
    s=0
    for j in range(1,(l-1)//2+1): s=(s+inv(j,l))%l
    return s
print("  candidate closed forms for delta_l (mod l):")
test("delta == 0", lambda l,a,g: 0)
test("delta == a*H_{(l-1)/6}", lambda l,a,g: a*H16(l))
test("delta == -a*H_{(l-1)/6}", lambda l,a,g: -a*H16(l))
test("delta == a*(H_{(l-1)/2}-H_{(l-1)/6})", lambda l,a,g: a*(H12(l)-H16(l)))
test("delta == a*H_{(l-1)/2}", lambda l,a,g: a*H12(l))
test("delta*a == const*l/a ... (a*delta invariant)", lambda l,a,g: a)  # sanity

# regression: express delta ≡ a*(x*H16 + y) mod l for small integer x,y
print("  small-combo search delta == a*(x*H16 + y*H12) mod l, x,y in [-6,6]:")
found=[]
for x in range(-6,7):
    for y in range(-6,7):
        if all((delta[l]-a_count(l)*(x*H16(l)+y*H12(l)))%l==0 for l in splits):
            found.append((x,y))
print(f"    solutions (x,y): {found if found else 'none'}")

# Kummer/Lehmer form: delta == a * (2 q_2 + ...)?  already excluded (v1). Try
# delta == c * (Bernoulli-like)  B_{l-2}? -> emulate via H sums above.
# Report the actual invariant a*delta for eyeballing:
print("  invariant  a_l * delta_l (mod l):")
for l in splits[:12]:
    a=a_count(l); print(f"    l={l:4d}: a*delta={a*delta[l]%l:4d}  H16={H16(l):4d}  "
                        f"a*H16={a*H16(l)%l:4d}  (a*delta)/H16={(a*delta[l]*inv(H16(l),l))%l if H16(l)%l else '-'}")
