#!/usr/bin/env python3
"""v2: (a) WHY four discriminants gave no instances -- the D = 5 mod 8 law;
       (b) fast Cornacchia-Smith sampling to raise power on Arms 2 and 3;
       (c) explicit power reporting for every null.
Exact integers; verdicts from exact permutation counts."""
from math import isqrt, gcd
import random, sys

_S = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113]
def is_prime(m, bases=(2,3,5,7,11,13,17,19,23,29,31,37)):
    if m < 2: return False
    for q in _S:
        if m % q == 0: return m == q
    d, s = m-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in bases:
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def tonelli(a, p):
    a %= p
    if a == 0: return 0
    if pow(a, (p-1)//2, p) != 1: return None
    if p % 4 == 3: return pow(a, (p+1)//4, p)
    q, s = p-1, 0
    while q % 2 == 0: q //= 2; s += 1
    z = 2
    while pow(z, (p-1)//2, p) != p-1: z += 1
    m, c, tt, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q+1)//2, p)
    while tt != 1:
        i, t2 = 0, tt
        while t2 != 1: t2 = t2*t2 % p; i += 1
        b = pow(c, 1 << (m-i-1), p)
        m, c = i, b*b % p
        tt = tt*c % p; r = r*b % p
    return r

def cornacchia_smith(p, absD):
    """4p = t^2 + absD*v^2 ; D = -absD < 0. Returns (t>0, v) or None."""
    D = -absD
    x0 = tonelli(D % p, p)
    if x0 is None: return None
    if (x0 - D) % 2 != 0: x0 = p - x0
    a, b = 2*p, x0
    c = isqrt(4*p)
    while b > c: a, b = b, a % b
    r = 4*p - b*b
    if r % absD: return None
    v2 = r // absD
    v = isqrt(v2)
    if v*v != v2 or v == 0: return None
    return (b, v)

# ---------- (a) which D admit prime order at all? ----------
print("=== (a) which CM discriminants admit ODD (hence possibly prime) group order? ===")
print(f"  {'D':>6} {'D mod 8':>8} {'2 in K':>8} {'twists':>8} {'odd n':>7} {'prime n':>8}")
def sieve(N):
    s = bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2, isqrt(N)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]
PR = sieve(120000)
for absD in (3,4,7,8,11,15,19,20,24,35,40,43,51,67,91,115,123,163,187,235,267,403,427):
    D = -absD
    tw = odd = pr = 0
    for p in PR:
        if p < 5: continue
        rep = cornacchia_smith(p, absD)
        if rep is None: continue
        t0, v = rep
        ts = [t0, -t0]
        if absD == 3: ts += [(t0+3*v)//2, -((t0+3*v)//2), (t0-3*v)//2, -((t0-3*v)//2)]
        if absD == 4: ts += [2*v, -2*v]
        for t in ts:
            if t*t > 4*p: continue
            n = p+1-t
            if n <= 3: continue
            tw += 1
            if n % 2 == 1:
                odd += 1
                if is_prime(n): pr += 1
    # 2 is inert in Q(sqrt(D)) iff D = 5 mod 8
    beh = "inert" if D % 8 == 5 else ("split" if D % 8 == 1 else "ramified")
    print(f"  {D:>6} {D % 8:>8} {beh:>8} {tw:>8} {odd:>7} {pr:>8}")
    sys.stdout.flush()
print("  PREDICTION: odd n possible  <=>  2 INERT  <=>  D = 5 mod 8")

# ---------- (b) high-power arms ----------
def perm_p(A, B, rnd, shuffles=20000):
    obs = sum(1 for a,b in zip(A,B) if a and b)
    Bl = list(B); ge = 0
    for _ in range(shuffles):
        rnd.shuffle(Bl)
        if sum(1 for a,b in zip(A,Bl) if a and b) >= obs: ge += 1
    return obs, ge, shuffles

def sample(absD, ell, target, bits, rnd, cap=4000000):
    A=[]; B=[]; C=[]
    tries = 0
    while len(A) < target and tries < cap:
        tries += 1
        p = rnd.randrange(1 << (bits-1), 1 << bits)
        p -= (p % ell) - 1
        if p % 2 == 0: p += ell
        if p % ell != 1 or p < 7 or not is_prime(p, bases=(2,3,5,7,11,13)): continue
        rep = cornacchia_smith(p, absD)
        if rep is None: continue
        t0, v = rep
        ts = [t0, -t0]
        if absD == 3: ts += [(t0+3*v)//2, -((t0+3*v)//2), (t0-3*v)//2, -((t0-3*v)//2)]
        for t in ts:
            if t*t > 4*p or t == 1: continue
            n = p+1-t
            if n <= 3 or n % ell != 1 or not is_prime(n, bases=(2,3,5,7,11,13)): continue
            pm = p % n
            if pm == 0: continue
            A.append(pow(pm, (n-1)//ell, n) == 1)
            B.append(pow(n % p, (p-1)//ell, p) == 1)
            C.append(pow(rnd.randrange(2,n), (n-1)//ell, n) == 1)
            if len(A) >= target: break
    return A, B, C

rnd = random.Random(8675309)
print("\n=== (b) association test, high power.  E = expected agreements under independence.")
print("    power quoted vs an ARM-1-SIZED effect (ratio 1.62): z = 0.62*sqrt(E) ===")
print(f"  {'family':>16} {'N':>6} {'agree':>6} {'E':>7} {'ratio':>6} {'perm p':>13} {'power(z)':>9} {'ctl':>10}")
def report(label, A, B, C, rnd):
    N = len(A)
    if N < 60:
        print(f"  {label:>16} {N:>6}   -- too few instances to test"); return
    E = sum(A)*sum(B)/N
    obs, ge, sh = perm_p(A, B, rnd)
    co, cg, _ = perm_p(C, B, rnd)
    power = 0.62*(E**0.5)
    verdict = "ASSOC" if (ge+1)/(sh+1) < 0.001 else "absent"
    ctl = "*** FIRED ***" if (cg+1)/(sh+1) < 0.001 else "clean"
    print(f"  {label:>16} {N:>6} {obs:>6} {E:>7.1f} {obs/E if E else 0:>6.2f}"
          f" {ge+1:>6}/{sh+1:<6} {power:>9.1f} {ctl:>10}  {verdict}")
    sys.stdout.flush()

A,B,C = sample(3, 3, 6000, 30, rnd); report("POS CTL D=-3 l=3", A,B,C, rnd)
for ell in (5, 7, 11, 13):
    A,B,C = sample(3, ell, 6000, 28, rnd); report(f"D=-3 l={ell}", A,B,C, rnd)
for absD in (11, 19, 43, 67, 163):
    A,B,C = sample(absD, 3, 6000, 30, rnd); report(f"D=-{absD} l=3", A,B,C, rnd)
