#!/usr/bin/env python3
"""Observation only. The order-8 outcome taxonomy (docs/n8 RUNNING_LOG E325; LonelyRunner/experiments/nN/redo/
taxo_outcome_classes_v1.md) carried to order 6 with 8 -> 6, applied to primitive SixResidual <= 40 and all primitive
5-sets <= 30. Readings rho_y = d_y/d_1, R = 6 d_1 t (start R = 1 is t = 1/(6 d_1)). Zone (y,j): 6j-1 < R rho_y < 6j+1,
entry (6j-1)/rho_y, exit (6j+1)/rho_y. Strip reading: |rho_y - 6j| < 1 for some j >= 1.
Cascade: R := 1; while some zone contains R, R := largest exit among them. Landing R*, nm jumps.
Opener (s,j): zone with exit R*; ties: smallest entry, then highest rank. Closer (c,k): least entry >= R*, k >= 1, lowest
rank on ties; width = entry - R*. Classes (test order: nm; width = 0; closer = s; opener lap; opener strip):
K0, K0z, K1a, K1b, K1s1, K1s2, K1z, K2a, K2b, K2c, K2d, K2s1, K2s2, K2z.
Also cross-tabulated with E76's slack depth (four / three / two runners with room around the cascade instant)."""
from fractions import Fraction as F
from collections import Counter, defaultdict
from itertools import combinations
import math
exec(open("cascade_vs_window_v1.py").read().split('print("(1) family')[0])
def taxo(S):
    rho = [F(d, S[0]) for d in S]
    def zones(R): return [(y, j) for y in range(5) for j in [round(R * rho[y] / 6)] if j >= 1 and 6 * j - 1 < R * rho[y] < 6 * j + 1]
    R = F(1); nm = 0
    while True:
        Z = zones(R)
        if not Z: break
        R = max(F(6 * j + 1) / rho[y] for y, j in Z); nm += 1
    Rs = R
    if nm == 0: s, j = None, None
    else:
        cands = [(y, jj) for y in range(5) for jj in range(1, 400) if F(6 * jj + 1) / rho[y] == Rs]
        s, j = min(cands, key=lambda z: (F(6 * z[1] - 1) / rho[z[0]], -z[0]))
    best = None
    for y in range(5):
        k = max(1, math.ceil((Rs * rho[y] + 1) / 6))
        while F(6 * k - 1) / rho[y] < Rs: k += 1
        e = F(6 * k - 1) / rho[y]
        if best is None or e < best[0] or (e == best[0] and y < best[1]): best = (e, y, k)
    width = best[0] - Rs; c = best[1]
    strip = s is not None and any(abs(rho[s] - 6 * jj) < 1 for jj in range(1, 400))
    if nm == 0: return "K0z" if width == 0 else "K0"
    if width == 0: return "K1z" if nm == 1 else "K2z"
    if c == s: return ("K1s" if nm == 1 else "K2s") + ("1" if j == 1 else "2")
    if nm == 1: return "K1a" if j == 1 else "K1b"
    if j == 1: return "K2a" if strip else "K2c"
    return "K2b" if strip else "K2d"
def depth(S):
    T, b = cascade(S); R4 = tuple(d for d in S if d != b)
    if slack_in(R4, *window(R4, T)): return "four"
    if any(slack_in(R, *window(R, T), q=F(1, 4)) for R in combinations(S, 3)): return "three"
    if any(slack_in(R, *window(R, T), q=F(1, 3)) for R in combinations(S, 2)): return "two"
    return "none"
rows = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]]
c6 = Counter(); cross = defaultdict(Counter)
for S in rows:
    k = taxo(S); c6[k] += 1; cross[depth(S)][k] += 1
print("SixResidual <= 40:", len(rows), "sets;", len(c6), "classes:", dict(sorted(c6.items())))
for dp in ("four", "three", "two", "none"): print(f"   slack depth {dp}:", dict(sorted(cross[dp].items())))
S0 = (2, 9, 13, 36, 40); print("(2,9,13,36,40):", taxo(S0), "depth", depth(S0))
call = Counter()
for S in combinations(range(1, 31), 5):
    if math.gcd(*S) == 1: call[taxo(S)] += 1
print("all primitive 5-sets <= 30:", sum(call.values()), "sets;", len(call), "classes:", dict(sorted(call.items())))
