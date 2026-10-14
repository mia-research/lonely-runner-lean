"""INTERIOR WITNESS NORMALISATION (candidate): every profile has a witness at which some
constraint is TIGHT -- q mod b = L(b) or U(b).  That is the nearest admissible lattice point to a
bad-interval boundary, which is what integrality allows when the boundary itself is unreachable.

Test at scale, and outside the divisor-closed category."""
from itertools import combinations
from math import gcd
import random

def I(b): return (-(-(b-1)//8), (7*b-1)//8)
def ok(q, m, bs): return all(I(b)[0] <= q % b <= I(b)[1] for b in bs + [m])
def edge_ok(m, bs):
    for b in bs + [m]:
        for e in I(b):
            q = e % b
            while q < m:
                if ok(q, m, bs): return True
                q += b
    return False
def any_ok(m, bs):
    return any(ok(q, m, bs) for q in range(m))

rng = random.Random(20260919)
print("A. divisor-closed, exhaustive")
for hi in (320, 500):
    tot = miss = 0
    for m in range(24, hi):
        ds = [d for d in range(2, m) if m % d == 0]
        if len(ds) < 5: continue
        for c in combinations(ds, 5):
            bs = sorted(c)
            if not any_ok(m, bs): continue
            tot += 1
            if not edge_ok(m, bs): miss += 1
    print(f"   m < {hi:<4}  {tot:>8,} profiles   no edge witness {miss}")

print("\nB. divisor-closed, larger m, sampled")
tot = miss = 0
for _ in range(1500):
    m = rng.randrange(500, 4000)
    ds = [d for d in range(2, m) if m % d == 0]
    if len(ds) < 5: continue
    bs = sorted(rng.sample(ds, 5))
    if not any_ok(m, bs): continue
    tot += 1
    if not edge_ok(m, bs): miss += 1
print(f"   500 <= m < 4000  {tot:,} profiles   no edge witness {miss}")

print("\nC. NOT divisor-closed: arbitrary moduli (b need not divide m)")
tot = miss = 0
for _ in range(4000):
    m = rng.randrange(40, 900)
    bs = sorted(rng.sample(range(2, m), 5))
    if not any_ok(m, bs): continue
    tot += 1
    if not edge_ok(m, bs): miss += 1
print(f"   arbitrary moduli  {tot:,} profiles   no edge witness {miss}")
