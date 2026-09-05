#!/usr/bin/env python3
"""OOS retest + conditional map of  (p/n)  over the j=0 family.

IN-SAMPLE was p < 300000. This run uses DISJOINT p in [300000, 900000].
Frozen question (before running): does the  n = 1 mod 8  excess of (p/n)=+1 replicate?
Control in EVERY cell: a seeded random base mod the same n.
Exact integers only.
"""
from math import isqrt
from collections import defaultdict
import random

LO, HI = 300000, 900000

def sieve_range(lo, hi):
    s = bytearray([1])*(hi+1); s[0]=s[1]=0
    for i in range(2, isqrt(hi)+1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(lo, hi+1) if s[i]]

def is_sq(x):
    if x < 0: return False
    r = isqrt(x); return r*r == x

def rep_4p(p):
    for M in range(1, isqrt((4*p)//27)+1):
        r = 4*p - 27*M*M
        if r <= 0: break
        if is_sq(r): return isqrt(r), M
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

rnd = random.Random(777)
rows = []
for p in sieve_range(LO, HI):
    if p % 3 != 1: continue
    rep = rep_4p(p)
    if rep is None: continue
    L, M = rep
    if (L + 9*M) % 2 != 0: continue
    for t in {L, -L, (L+9*M)//2, -((L+9*M)//2), (L-9*M)//2, -((L-9*M)//2)}:
        n = p + 1 - t
        if n <= 3 or n % 3 != 1 or not is_prime(n): continue
        e2 = (n-1)//2
        rows.append(dict(p=p, t=t, n=n, v=3*M,
                         psq = pow(p % n, e2, n) == 1,
                         ctl = pow(rnd.randrange(2, n), e2, n) == 1))

N = len(rows)
print(f"OOS instances (p in [{LO},{HI}], n prime, n=1 mod 3): {N}\n")

def table(keyfn, label):
    d = defaultdict(lambda: [0,0,0])
    for r in rows:
        k = keyfn(r)
        d[k][0] += 1; d[k][1] += r["psq"]; d[k][2] += r["ctl"]
    print(f"=== (p/n)=+1 rate, split by {label} ===")
    print(f"  {'cell':>18} {'N':>6} {'p is sq':>9} {'rate':>8} {'ctl rate':>9} {'z(p)':>7}")
    for k in sorted(d):
        tot, hit, ctl = d[k]
        sd = (tot*0.25) ** 0.5
        z = (hit - tot/2)/sd if sd > 0 else 0
        print(f"  {str(k):>18} {tot:>6} {hit:>9} {hit/tot:>8.4f} {ctl/tot:>9.4f} {z:>+7.2f}")
    print()

table(lambda r: r["n"] % 8, "n mod 8")
table(lambda r: r["p"] % 8, "p mod 8")
table(lambda r: (r["n"] % 8, r["p"] % 8), "(n mod 8, p mod 8)")
table(lambda r: r["t"] % 4, "t mod 4")
table(lambda r: (r["n"] % 8, r["t"] % 4), "(n mod 8, t mod 4)")
table(lambda r: r["v"] % 8, "v mod 8  (v=3M)")

# the reciprocity identity: for n = 1 mod 4, (p/n) = (n/p) = ((1-t)/p)
def leg(a, q):
    a %= q
    if a == 0: return 0
    return 1 if pow(a, (q-1)//2, q) == 1 else -1
ok = bad = 0
for r in rows:
    if r["n"] % 4 != 1: continue
    lhs = 1 if r["psq"] else -1
    rhs = leg(1 - r["t"], r["p"])
    if lhs == rhs: ok += 1
    else: bad += 1
print(f"=== reciprocity self-test, n=1 mod 4:  (p/n) == ((1-t)/p) : {ok} ok, {bad} bad ===")
