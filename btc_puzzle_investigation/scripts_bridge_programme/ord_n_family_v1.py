#!/usr/bin/env python3
"""H-sextic family test: is `p a 6th power mod n` FORCED for j=0 curves, or a 1-in-6 draw?

Family: for p = 1 mod 3, 4p = L^2 + 27M^2; the six sextic twists of y^2=x^3+b have
traces t in {+-L, +-(L+9M)/2, +-(L-9M)/2}; n = p+1-t. Keep n prime with n = 1 mod 3.
Exact integers only.
"""
from math import isqrt
from collections import Counter
import random

LIMIT = 300000

def sieve_upto(N):
    s = bytearray([1])*(N+1); s[0]=s[1]=0
    for i in range(2, isqrt(N)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(N+1) if s[i]]

def is_sq(x):
    if x < 0: return False
    r = isqrt(x); return r*r == x

def rep_4p(p):
    """4p = L^2 + 27 M^2, M>0, L>0."""
    for M in range(1, isqrt((4*p)//27)+1):
        r = 4*p - 27*M*M
        if r <= 0: break
        if is_sq(r):
            return isqrt(r), M
    return None

def is_prime(m):
    if m < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m % q == 0: return m == q
    d, s = m-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, m)
        if x in (1, m-1): continue
        for _ in range(s-1):
            x = x*x % m
            if x == m-1: break
        else: return False
    return True

primes = sieve_upto(LIMIT)
rnd = random.Random(20260724)

rows = []
for p in primes:
    if p % 3 != 1 or p < 7: continue
    rep = rep_4p(p)
    if rep is None: continue
    L, M = rep
    traces = {L, -L, (L+9*M)//2, -((L+9*M)//2), (L-9*M)//2, -((L-9*M)//2)}
    for t in traces:
        if (L+9*M) % 2 != 0: continue
        n = p + 1 - t
        if n <= 3 or not is_prime(n): continue
        if n % 3 != 1: continue           # else cube char is trivial
        if p % n == 0: continue
        e2, e3, e6 = (n-1)//2, (n-1)//3, (n-1)//6
        pm = p % n
        rows.append(dict(
            p=p, t=t, n=n,
            p_sq  = pow(pm, e2, n) == 1,
            p_cu  = pow(pm, e3, n) == 1,
            p_6th = pow(pm, e6, n) == 1,
            # --- controls: unrelated bases against the SAME n ---
            c5_cu = pow(5 % n, e3, n) == 1 if n != 5 else None,
            cr_cu = pow(rnd.randrange(2, n), e3, n) == 1,
            cr_sq = pow(rnd.randrange(2, n), e2, n) == 1,
            # --- is it t, or p, that carries it? ---
            t_cu  = (pow((t) % n, e3, n) == 1) if t % n != 0 else None,
            v_cu  = pow((3*M) % n, e3, n) == 1 if (3*M) % n != 0 else None,
        ))

N = len(rows)
print(f"family instances (p=1 mod3, n prime, n=1 mod3): {N}   p < {LIMIT}")

def rate(key):
    vals = [r[key] for r in rows if r[key] is not None]
    return sum(vals), len(vals)

print("\n=== TARGET ===")
for k, expect in (("p_sq","1/2"), ("p_cu","1/3"), ("p_6th","1/6")):
    h, tot = rate(k)
    print(f"  {k:>6}: {h:>6}/{tot}  = {h}/{tot}   (chance {expect} -> {tot}*{expect} = {eval(expect)*tot:.1f})")

print("\n=== CONTROLS (same n, unrelated bases) ===")
for k, expect in (("c5_cu","1/3"), ("cr_cu","1/3"), ("cr_sq","1/2")):
    h, tot = rate(k)
    print(f"  {k:>6}: {h:>6}/{tot}   (chance {expect} -> {eval(expect)*tot:.1f})")

print("\n=== IS IT p, OR t/v? ===")
for k, expect in (("t_cu","1/3"), ("v_cu","1/3")):
    h, tot = rate(k)
    print(f"  {k:>6}: {h:>6}/{tot}   (chance {expect} -> {eval(expect)*tot:.1f})")

# if p_cu is universal, look for what breaks p_sq
sq_fail = [r for r in rows if not r["p_sq"]]
print(f"\np NOT a square mod n: {len(sq_fail)}/{N}")
if sq_fail:
    print("  n mod 8 among those:", Counter(r['n'] % 8 for r in sq_fail))
    print("  n mod 8 among ALL  :", Counter(r['n'] % 8 for r in rows))
    print("  t mod 4 among those:", Counter(r['t'] % 4 for r in sq_fail))
cu_fail = [r for r in rows if not r["p_cu"]]
print(f"p NOT a cube  mod n: {len(cu_fail)}/{N}")
if cu_fail[:5]:
    print("  first few:", [(r['p'], r['t'], r['n']) for r in cu_fail[:5]])
