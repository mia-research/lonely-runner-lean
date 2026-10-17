#!/usr/bin/env python3
"""Local search for a counterexample to Claim A (EXACT masks): runner (u, C), u a unit mod 343, C in Z/343; allowed set
A(u, C) = {k in Z/343 : top digit of (u k + C) mod 343 in {1..5}} (343-bit).  Five runners with empty intersection
would refute Claim A.  Hill climbing with restarts on |intersection|, moves change one runner's (u, C)."""
import random
N = 343
units = [u for u in range(1, N) if u % 7]
def mask(u, C):
    m = 0
    for k in range(N):
        if 1 <= ((u * k + C) % N) // 49 <= 5: m |= 1 << k
    return m
cache = {}
def M(u, C):
    if (u, C) not in cache: cache[(u, C)] = mask(u, C)
    return cache[(u, C)]
rnd = random.Random(5); best = N; ex = []
for restart in range(300):
    R = [(rnd.choice(units), rnd.randrange(N)) for _ in range(5)]
    def size(R):
        m = (1 << N) - 1
        for r in R: m &= M(*r)
        return bin(m).count("1")
    cur = size(R)
    for it in range(4000):
        j = rnd.randrange(5)
        if rnd.random() < 0.5: cand = (R[j][0], rnd.randrange(N))
        else: cand = (rnd.choice(units), R[j][1])
        R2 = R[:]; R2[j] = cand; s = size(R2)
        if s <= cur: R, cur = R2, s
        if cur == 0: break
    best = min(best, cur)
    if cur == 0: ex.append(R)
    if len(ex) >= 3: break
print(f"best |intersection| over restarts: {best}; counterexamples to Claim A found: {len(ex)}")
for e in ex: print("   ", e)
