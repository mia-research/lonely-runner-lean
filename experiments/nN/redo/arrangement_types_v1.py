"""Arrangement types through the cascade (2026-09-25).  Exact (Fraction) throughout; arrangements are 8
distinct POSITIVE integer speeds; every runner is evaluated in its own readings (MANUSCRIPT_v21 s1.1).

Per runner: the cascade's event t*, its moves, and u* = d_min * t* (laps of the nearest runner).
"First cycle" = u* <= 1 (the event falls inside the nearest runner's first relative lap).
Slot sharing, read at the subject's own AP scale d_min: reading s = d/d_min; its distance to the subject's
slot is delta(s) = distance from s to the nearest multiple of 8 (in eighths of the AP spacing).  A runner with
delta < 1 is in the subject's slot zone at the AP's first spine point u = 1/8.

Part 2 (the 56): for separated core + compact train, the TrainCollapseN instant at ratios N/m below 56."""
import random, sys
from fractions import Fraction as F
from math import floor
from collections import defaultdict
from arrangement_lib import readings, nd

CAP = 5000
def cascade(ds, q=8):
    t = F(1, q * min(ds)); n = 0
    while n < CAP:
        way = [d for d in ds if nd(d * t) < F(1, q)]
        if not way: return t, n
        t = max((F(floor(d * t - F(1, q)) + 1) + F(1, q)) / d for d in way); n += 1
    return None, n

def delta8(s):                     # distance of a reading (in d_min units) to the nearest multiple of 8
    r = s % 8
    return min(r, 8 - r)

def ok(V):
    return len(V) == 8 and len(set(V)) == 8 and min(V) > 0

rnd = random.Random(20260925)
fam = defaultdict(list)
# A. deformed AP, gap 840, deviations up to rho gaps
for rho in (F(1, 100), F(1, 8), F(1, 2), F(2)):
    while len(fam[f'A AP+dev rho={rho}']) < 60:
        V = [840 * (k + 1) + rnd.randint(-int(rho * 840), int(rho * 840)) for k in range(8)]
        V = [v + 2000 for v in V]
        if ok(V): fam[f'A AP+dev rho={rho}'].append(V)
# B. uniform random
for hi in (40, 1000):
    while len(fam[f'B uniform [1,{hi}]']) < 60:
        V = rnd.sample(range(1, hi + 1), 8); fam[f'B uniform [1,{hi}]'].append(V)
# C/D. separated: core of c runners below 30, train of 8-c runners at N + offsets; compact vs spread
for c in (3, 4, 5):
    for kind, spread in (('C compact train', 'small'), ('D spread train', 'large')):
        key = f'{kind} core={c}'
        while len(fam[key]) < 40:
            N = rnd.choice((2000, 10**4))
            core = rnd.sample(range(1, 30), c)
            if spread == 'small':
                offs = rnd.sample(range(0, 30), 8 - c)
            else:
                offs = rnd.sample(range(0, 7 * N), 8 - c)   # train members spread up to 8x its slowest
            V = core + [N + e for e in offs]
            if ok(V): fam[key].append(V)
# E. near-coincident pairs (four tight pairs)
while len(fam['E four close pairs']) < 60:
    base = rnd.sample(range(10, 400), 4); w = rnd.randint(1, 3)
    V = [b for b in base] + [b + w for b in base]
    if ok(V): fam['E four close pairs'].append(V)
# F. geometric
for r in (F(3, 2), F(2), F(3)):
    V = [int(1000 * r**k) for k in range(8)]
    fam['F geometric'].append(V)
# G. near-wrap (1..7, 9 +/- delta), scaled by 1000
for dl in (1, 3, 10, 50):
    for sgn in (1, -1):
        fam['G near-wrap'].append([1000 * k for k in range(1, 8)] + [9000 + sgn * dl])
# H. residual sets of MANUSCRIPT_v21 s17D, realised as (1, 1 + r...)
for S in [(2,12,15,21,32,34,38), (4,5,6,8,14,32,37), (4,5,6,14,16,34,38), (4,5,6,14,17,32,38),
          (4,5,6,14,32,34,38), (4,6,14,15,16,34,38), (4,7,8,15,29,36,37)]:
    fam['H residual [1,40]'].append([1] + [1 + r for r in S])
# I. recorded hard cases
fam['I hard cases'] += [[27,70,107,137,159,188,344,393], [1,31,75,97,128,160,176,225],
                        [1,1975,5265,6910,8737,9589,11845,15135]]

print("PART 1. Arrangement types, every runner.  u* = d_min t*; first cycle = u* <= 1.")
print(f"{'family':32s} {'runners':>7s} {'u*<=1/8':>8s} {'u*<=1':>6s} {'u*>1':>5s} {'max moves':>9s} {'max u*':>10s}")
late_rows = []; early_rows = []
for key, arrs in fam.items():
    n = a = b = c = 0; mm = 0; mu = F(0)
    for V in arrs:
        for k in range(8):
            ds = readings(V, k); t, moves = cascade(ds)
            assert t is not None, (V, k)
            u = min(ds) * t; n += 1; mm = max(mm, moves); mu = max(mu, u)
            if u <= F(1, 8): a += 1
            if u <= 1: b += 1
            else: c += 1
            dmin = min(ds)
            sub = sorted(delta8(F(d, dmin)) for d in ds)          # subject-slot distances at scale d_min
            row = (key, V, k, u, moves, sub[0])
            (late_rows if u > 1 else early_rows).append(row)
    print(f"{key:32s} {n:7d} {a:8d} {b:6d} {c:5d} {mm:9d} {str(mu):>10s}")

print("\nSubject-slot test: smallest distance (in AP eighths, at scale d_min) of any other runner's reading from a")
print("multiple of 8, i.e. from the subject's own slot.  delta = 0 exact sharer; delta < 1 in the slot zone at u = 1/8.")
def bucket(x):
    return '0 (exact)' if x == 0 else ('(0,1/8)' if x < F(1, 8) else ('[1/8,1)' if x < 1 else '>=1'))
for name, rows in (('events after the first cycle (u* > 1)', late_rows), ('events in the first cycle (u* <= 1)', early_rows)):
    cnt = defaultdict(int)
    for r in rows: cnt[bucket(r[5])] += 1
    print(f"  {name}: {len(rows)} runners -> " + ", ".join(f"{b_}: {cnt[b_]}" for b_ in ('0 (exact)', '(0,1/8)', '[1/8,1)', '>=1')))
print("\nEvery event after the first cycle:")
for key, V, k, u, moves, d0 in late_rows:
    print(f"  {key:26s} V={V} runner {V[k]}: u*={u} moves={moves} nearest-to-slot delta={d0}")

# ---------------- Part 2: the 56 ----------------
print("\nPART 2. TrainCollapseN's instant below N = 56 m.  Core C, compact train {N+e}, all <= m.")
def collapse_instant(C, E, N):
    Es = sorted(E); best = None
    for i, j in zip(Es, Es[1:]):
        R = sorted({2 * c for c in C} | {abs(2 * e - i - j) for e in Es})
        tau, _ = cascade(R, q=7)
        y = (i + j) * tau; t0 = 2 * tau
        t = t0 + ((-y - N * t0) % 1) / N
        allds = list(C) + [N + e for e in Es]
        if all(nd(d * t) >= F(1, 8) for d in allds):
            return True
    return False
for ratio in (56, 40, 30, 20, 15, 12, 9):
    tot = good = 0
    rr = random.Random(ratio)
    while tot < 300:
        f = rr.choice((3, 4, 5, 6)); m = 40
        C = rr.sample(range(1, m + 1), 7 - f); E = [0] + rr.sample(range(1, m + 1), f - 1)
        N = ratio * m
        if len(set(C) | {N + e for e in E}) < 7: continue
        tot += 1; good += collapse_instant(C, E, N)
    print(f"  N = {ratio:2d} m: collapse instant lonely at 1/8 in {good} of {tot}")
