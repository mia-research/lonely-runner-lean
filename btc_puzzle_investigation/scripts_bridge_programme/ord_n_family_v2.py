#!/usr/bin/env python3
"""CORRECTED j=0 family sampler + scale sweep.

BUG IN v1: used 4p = L^2 + 27M^2, which is solvable ONLY when 2 is a cubic residue
mod p (classical). That silently restricted the family to a residue-selected subset
-- a conditioning that can manufacture character bias. FIXED HERE:

  p = 1 mod 3  =>  p = a^2 + 3b^2 ALWAYS solvable (Cornacchia).
  pi = a + b*sqrt(-3);  associates +-pi, +-pi*w, +-pi*w^2 have traces
      +-2a, +-(a+3b), +-(a-3b).
  n = p+1-t.  t=+-2a gives n EVEN (never odd prime order) -> dropped.
  a,b always opposite parity => a+-3b always odd => those 4 twists give odd n.

Exact integers only.
"""
from math import isqrt, gcd
from collections import defaultdict
import random

# ---------- primality / sqrt / cornacchia ----------
_SMALL = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
def is_prime(m, bases=(2,3,5,7,11,13,17,19,23,29,31,37)):
    if m < 2: return False
    for q in _SMALL:
        if m % q == 0: return m == q
    d, s = m-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in bases:
        a %= m
        if a == 0: continue
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

def sqrt_m3(p, rnd):
    """sqrt(-3) mod p for p = 1 mod 3, via a primitive cube root of unity: (2w+1)^2 = -3."""
    while True:
        g = rnd.randrange(2, p)
        w = pow(g, (p-1)//3, p)
        if w != 1:
            return (2*w + 1) % p

def cornacchia3(p, rnd):
    """p = a^2 + 3 b^2 for prime p = 1 mod 3."""
    r = sqrt_m3(p, rnd)
    if r < p - r: r = p - r          # take the larger root
    a, b = p, r
    lim = isqrt(p)
    while b > lim:
        a, b = b, a % b
    c = p - b*b
    if c % 3: return None
    y2 = c // 3
    y = isqrt(y2)
    if y*y != y2: return None
    return (b, y)

def jacobi(a, n):
    """Jacobi symbol (a/n), n odd > 0."""
    assert n > 0 and n % 2 == 1
    a %= n; res = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5): res = -res
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3: res = -res
        a %= n
    return res if n == 1 else 0

def twists(p, rnd):
    """the 4 odd-order j=0 twist orders n = p+1-t."""
    rep = cornacchia3(p, rnd)
    if rep is None: return []
    a, b = rep
    assert a*a + 3*b*b == p, "cornacchia failed"
    out = []
    for t in (a+3*b, -(a+3*b), a-3*b, -(a-3*b)):
        n = p + 1 - t
        if n > 2 and n % 2 == 1:
            out.append((t, n))
    return out

# ================= PART A: small scale, n PRIME, full character set =============
def sieve(N):
    s = bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2, isqrt(N)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]

rnd = random.Random(20260724)
print("=== PART A: corrected family, n prime, p < 300000 (matches v1's range) ===")
rows = []
for p in sieve(300000):
    if p % 3 != 1 or p < 7: continue
    for t, n in twists(p, rnd):
        if n % 3 != 1 or not is_prime(n): continue
        if p % n == 0: continue
        e2, e3, e6 = (n-1)//2, (n-1)//3, (n-1)//6
        pm = p % n
        rows.append(dict(p=p, t=t, n=n,
                         psq=pow(pm,e2,n)==1, pcu=pow(pm,e3,n)==1, p6=pow(pm,e6,n)==1,
                         csq=pow(rnd.randrange(2,n),e2,n)==1,
                         ccu=pow(rnd.randrange(2,n),e3,n)==1))
N = len(rows)
print(f"  instances: {N}")
for k, ch, lab in (("psq",0.5,"p is a square"), ("pcu",1/3,"p is a cube"), ("p6",1/6,"p is a 6th power"),
                   ("csq",0.5,"CONTROL square"), ("ccu",1/3,"CONTROL cube")):
    h = sum(r[k] for r in rows); sd = (N*ch*(1-ch))**0.5
    print(f"    {lab:>16}: {h:>6}/{N} = {h/N:.4f}   chance {ch:.4f}   z = {(h-N*ch)/sd:+.2f}")

print("\n  --- (p/n)=+1 split by n mod 8 (v1 claimed a +6.7 sigma excess at n=1) ---")
d = defaultdict(lambda: [0,0,0])
for r in rows:
    c = d[r["n"] % 8]; c[0]+=1; c[1]+=r["psq"]; c[2]+=r["csq"]
print(f"    {'n%8':>5} {'N':>6} {'rate':>8} {'ctl':>8} {'z':>7}")
for k in sorted(d):
    tot, hit, ctl = d[k]; sd=(tot*0.25)**0.5
    print(f"    {k:>5} {tot:>6} {hit/tot:>8.4f} {ctl/tot:>8.4f} {(hit-tot/2)/sd:>+7.2f}")

# ================= PART B: does anything survive to secp scale? =================
# Jacobi proxy (no primality needed on n) -- validated against the prime-n rate above.
print("\n=== PART B: scale sweep, Jacobi (p/n) over the corrected family ===")
print(f"  {'bits':>5} {'inst':>7} {'rate all':>9} {'ctl':>8} {'z':>7} | {'n=1(8) rate':>12} {'N':>6} {'z':>7}")
for bits in (16, 24, 32, 48, 64, 96, 128, 192, 256):
    target = 6000
    tot=hit=ctl=0; t1=h1=0
    tries = 0
    while tot < target and tries < 400000:
        tries += 1
        cand = rnd.randrange(1 << (bits-1), 1 << bits) | 1
        cand -= (cand - 1) % 3        # force = 1 mod 3
        if cand % 2 == 0: cand += 3
        if cand % 3 != 1 or not is_prime(cand, bases=(2,3,5,7,11,13)): continue
        p = cand
        for t, n in twists(p, rnd):
            if gcd(p % n, n) != 1: continue
            j = jacobi(p % n, n)
            if j == 0: continue
            tot += 1; hit += (j == 1)
            ctl += (jacobi(rnd.randrange(2, n), n) == 1)
            if n % 8 == 1:
                t1 += 1; h1 += (j == 1)
    sd = (tot*0.25)**0.5; sd1 = (t1*0.25)**0.5 if t1 else 1
    print(f"  {bits:>5} {tot:>7} {hit/tot:>9.4f} {ctl/tot:>8.4f} {(hit-tot/2)/sd:>+7.2f} |"
          f" {h1/t1 if t1 else 0:>12.4f} {t1:>6} {(h1-t1/2)/sd1:>+7.2f}")
