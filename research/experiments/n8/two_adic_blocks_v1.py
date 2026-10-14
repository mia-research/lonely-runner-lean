#!/usr/bin/env python3
"""2-adic block structure of the p=163 covering problem (k=7, n=8, N=1304, H=652).

CLAIM (derived, tested here).  Partition the 652 targets into the 163 residue
classes mod 163:  C_r = { r, r+163, r+326, r+489 },  each of size 4.
For j = r + 163 t,   j*v mod 1304 = (r*v mod 1304) + 163*((t*v) mod 8),
so inside a class a speed only shifts the "block index" a = floor((rv mod 1304)/163)
by (t*v) mod 8.  Covered means the block index lands in {0,7} (with the b>0 caveat
at 1141).  Hence the number of targets of C_r a speed can cover is capped by the
2-adic valuation e = v_2(v):

    e >= 3  ->  0 or 4   (all-or-nothing: this IS the Z/163 collapse)
    e == 2  ->  0 or 2   (a pair)
    e == 1  ->  0 or 1
    e == 0  ->  0, 1 or 2

Summed over 163 classes this reproduces the measured coverage sizes 164/162/163/162.
"""
from collections import Counter

N, H, p, n = 1304, 652, 163, 8

def covers(j, v):
    r = (j * v) % N
    return r < p or r > N - p

def v2(v):
    e = 0
    while v % 2 == 0:
        v //= 2; e += 1
    return e

speeds = [v for v in range(1, H + 1) if v % p != 0]
classes = [[r + p * t for t in range(4)] for r in range(1, p + 1)]  # r=1..163 covers 1..652

print("per-class coverage profile by 2-adic valuation of v")
print(f"{'e':>3} {'#speeds':>8} {'per-class counts seen':>34} {'total cov (min..max)':>22}")
prof = {}
tot = {}
for v in speeds:
    e = min(v2(v), 3)
    c = Counter(sum(1 for j in C if covers(j, v)) for C in classes)
    prof.setdefault(e, Counter()).update(c)
    tot.setdefault(e, []).append(sum(covers(j, v) for j in range(1, H + 1)))
for e in sorted(prof):
    seen = dict(sorted(prof[e].items()))
    print(f"{e:>3} {len(tot[e]):>8} {str(seen):>34} {str((min(tot[e]), max(tot[e]))):>22}")

cap = {0: 2, 1: 1, 2: 2, 3: 4}
bad = [(e, k) for e in prof for k in prof[e] if k > cap[e]]
print("\nCAP VIOLATIONS:", bad if bad else "none -- caps hold for every speed and every class")

# all-or-nothing check for e>=3
allnone = all(set(prof[3]) <= {0, 4} for _ in [0])
print("e>=3 all-or-nothing:", set(prof[3]) <= {0, 4})
print("e==2 pairs only    :", set(prof[2]) <= {0, 2})
print("e==1 singles only  :", set(prof[1]) <= {0, 1})
