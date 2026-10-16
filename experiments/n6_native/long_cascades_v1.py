#!/usr/bin/env python3
"""Observation only. What drives the most moves? Per order n = 4..7 (same exhaustive ranges as taxo_orders_v1), the
cascades with the most moves: their speeds, path of (setter rank, lap), landing R*, and per move the margin by which
the new instant clears the previous setter's entry ... recorded as: at each move, how many runners are in the way, and
the gap (in R units) between the instant reached and the next blocker's entry (how narrowly the next knot is tied)."""
import math
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
H = {4: 90, 5: 50, 6: 30, 7: 22}
def walk(S, n):
    rho = [F(d, S[0]) for d in S]; R = F(1); path = []; inway = []; gaps = []
    while True:
        Z = [(y, j) for y in range(len(S)) for j in [round(R * rho[y] / n)] if j >= 1 and n * j - 1 < R * rho[y] < n * j + 1]
        if not Z: return path, R, inway, gaps
        inway.append(len(Z))
        Rn = max(F(n * j + 1) / rho[y] for y, j in Z)
        y, j = max(Z, key=lambda z: (F(n * z[1] + 1) / rho[z[0]], -F(n * z[1] - 1) / rho[z[0]]))
        # gap: how far past Rn's own clearance is the nearest entry of any runner after Rn (smaller = narrower knot)
        nxt = min(F(n * k - 1) / rho[x] for x in range(len(S)) for k in [math.ceil((Rn * rho[x] + 1) / n) if True else 0] + [math.floor((Rn * rho[x]) / n) + 1] if F(n * k - 1) / rho[x] > Rn - 0 or True)
        path.append((y + 1, j)); R = Rn
for n in (4, 5, 6, 7):
    rows = []
    for S in combinations(range(1, H[n] + 1), n - 1):
        if math.gcd(*S) != 1: continue
        p, R, iw, _ = walk(S, n); rows.append((len(p), S, p, R, iw))
    rows.sort(key=lambda r: -r[0])
    dist = Counter(r[0] for r in rows)
    print(f"== n={n}: moves distribution (tail): {sorted(dist.items())[-8:]}")
    for r in rows[:6]:
        print(f"   moves {r[0]}: S={r[1]} R*={r[3]} (~{float(r[3]):.3f}) path={r[2]} in-the-way counts={r[4]}")
