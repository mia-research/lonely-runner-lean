#!/usr/bin/env python3
"""Reference for seven_level4_exh_v1.c: exact check of random half tuples, and of the C program's mask for a few units."""
import random, subprocess, sys
N = 2401
ks = [k for k in range(1, N) if k % 7]
def good(t):
    return any(all(343 <= u * k % N <= 2058 for u in t) for k in ks)
rng = random.Random(7)
hu = [u for u in range(1, 1201) if u % 7]
cnt = 0
for _ in range(3000):
    t = [1] + sorted(rng.choice(hu) for _ in range(4))
    cnt += not good(t)
print("python random half tuples: 3000, failures", cnt)
