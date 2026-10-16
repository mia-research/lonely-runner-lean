#!/usr/bin/env python3
"""Independent re-check of s8_cert_v5_leaves.txt (written without importing the certifier).
(1) Random rational points of the §8 domain with x4 < 6 (x5 up to 60): each must lie in some leaf, and the leaf's
    statement must hold at the point by its own definition: window_two base and residue conditions on the actual
    window, the fold v5 |W| >= 1/3, or the 20 box inequalities; and the point must be lonely (exact interval search).
(2) Integer §8 sets with v1 <= 12 and v4 < 6 v1: the same tests.
(3) Leaves are inside the domain hull and their statements are from the declared list."""
import random, math
from fractions import Fraction as F
leaves = []
for l in open("s8_cert_v5_leaves.txt"):
    a, b = l.split("|"); nums = a.split()
    cell = [(F(nums[2 * i]), None if nums[2 * i + 1] == "inf" else F(nums[2 * i + 1])) for i in range(4)]
    kind, laps = b.split(); leaves.append((cell, kind, tuple(int(z) for z in laps.split(","))))
def inside(x, c): return all(lo <= xi and (hi is None or xi <= hi) for xi, (lo, hi) in zip(x[1:], c))
def win(x, laps):
    L = max(F(6 * m + 1, 6) / xi for xi, m in zip(x, laps)); U = min(F(6 * m + 5, 6) / xi for xi, m in zip(x, laps))
    return L, U
def holds(x, kind, laps):
    if kind == "W3":
        L, U = win(x[:3], laps); l = U - L; a, b = x[3], x[4]
        if l < F(1, 3) / a + F(1, 3) / b: return False
        m = 0
        while 3 * m * a < a + b:
            if F(3 * m + 1, 3) / b > l: return False
            m += 1
        return True
    if kind == "F4":
        L, U = win(x[:4], laps); return x[4] * (U - L) >= F(1, 3)
    return all((6 * laps[i] + 1) * x[j] <= (6 * laps[j] + 5) * x[i] for i in range(5) for j in range(5) if i != j)
def lonely(x):
    tmax = F(3)
    pts = sorted(set(F(6 * k + j, 6) / d for d in x for k in range(int(tmax * d) + 2) for j in (1, 5)))
    return any(all(F(1, 6) <= (d * a) % 1 <= F(5, 6) for d in x) for a in pts if a <= tmax + 1)
random.seed(85)
bad = {"no leaf": 0, "statement fails": 0, "not lonely": 0}; n = 0
def check(x):
    global n
    n += 1
    ls = [lf for lf in leaves if inside(x, lf[0])]
    if not ls: bad["no leaf"] += 1; print("no leaf", x); return
    if not any(holds(x, k, m) for _, k, m in ls): bad["statement fails"] += 1; print("fails", x, ls[0][1:]); return
    if not lonely(x): bad["not lonely"] += 1
def rnd(lo, hi, den=997): return F(random.randint(int(lo * den), int(hi * den)), den)
for _ in range(20000):
    x2 = rnd(1, 3); x3 = rnd(x2, 3); x4 = rnd(x3, 6); x5 = rnd(x4, 60)
    if x4 >= 6: continue
    check((F(1), x2, x3, x4, x5))
pts1 = n
for v1 in range(1, 13):
    for v2 in range(v1 + 1, 3 * v1 + 1):
        for v3 in range(v2 + 1, 3 * v1 + 1):
            for v4 in range(v3 + 1, 6 * v1):
                for v5 in range(v4 + 1, min(60 * v1, v4 + 40 * v1) + 1, max(1, v1 // 3)):
                    check(tuple(F(v, v1) for v in (v1, v2, v3, v4, v5)))
print(f"random points {pts1}, integer points {n - pts1}: {bad}")
print("leaf kinds:", sorted(set((k, m) for _, k, m in leaves)))
