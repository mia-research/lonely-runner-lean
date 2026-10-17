#!/usr/bin/env python3
"""Claim A (shifted level 3), EXACT: for five units u mod 343 and shifts C in (Z/343)^5, is there k in Z/343 (any) with
top digit of (u k + C_u) mod 343 in {1..5} for every u?  Random (u, C) and, for random u, an adversarial search: choose
C greedily to kill the remaining good k (each runner's good set is the bijective image of the 245 residues with top
digit in {1..5}; C_u shifts it)."""
import random, sys
import numpy as np
N = 343
good_res = np.array([1 if 1 <= r // 49 <= 5 else 0 for r in range(N)], dtype=bool)
rnd = random.Random(2)
units = [u for u in range(1, N) if u % 7]
def goodset(u, c):
    return good_res[(u * np.arange(N) + c) % N]
rand_fail = 0
for _ in range(int(sys.argv[1])):
    U = [rnd.choice(units) for _ in range(5)]; C = [rnd.randrange(N) for _ in range(5)]
    m = np.ones(N, bool)
    for u, c in zip(U, C): m &= goodset(u, c)
    rand_fail += not m.any()
adv_fail = 0; ex = None
for _ in range(int(sys.argv[2])):
    U = [rnd.choice(units) for _ in range(5)]
    m = np.ones(N, bool); C = []
    for u in U:          # pick C_u minimising the surviving k
        best = min(range(N), key=lambda c: (m & goodset(u, c)).sum())
        m &= goodset(u, best); C.append(best)
    if not m.any():
        adv_fail += 1; ex = ex or (U, C)
print(f"random (u, C): {sys.argv[1]} trials, failures {rand_fail}")
print(f"adversarial C (greedy) for random u: {sys.argv[2]} trials, failures {adv_fail}; example {ex}")
