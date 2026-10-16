#!/usr/bin/env python3
"""Observation only. The outcome taxonomy (order-8 E325; order 6 E77) at orders n = 3..7, exhaustive over primitive
(n-1)-subsets of [1, H_n]. Readings rho = d/d_1, R = n d_1 t, zone (y,j): nj-1 < R rho_y < nj+1, entry (nj-1)/rho,
exit (nj+1)/rho; strip reading |rho - nj| < 1. Cascade from R = 1; opener = zone with exit R* (ties: smallest entry,
then highest rank); closer = least entry >= R* (k >= 1, lowest rank on ties). Classes as E325.
Also per order: realised (opener rank, closer rank) pairs, largest number of moves, largest landing R*."""
import sys, math
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
CLASSES = ["K0", "K0z", "K1a", "K1b", "K1s1", "K1s2", "K1z", "K2a", "K2b", "K2c", "K2d", "K2s1", "K2s2", "K2z"]
def taxo(S, n):
    m = len(S); rho = [F(d, S[0]) for d in S]
    R = F(1); nm = 0
    while True:
        Z = [(y, j) for y in range(m) for j in [round(R * rho[y] / n)] if j >= 1 and n * j - 1 < R * rho[y] < n * j + 1]
        if not Z: break
        R = max(F(n * j + 1) / rho[y] for y, j in Z); nm += 1
    Rs = R; s = j = None
    if nm:
        cands = [(y, jj) for y in range(m) for jj in [((Rs * rho[y]) - 1) / n] if jj.denominator == 1 and jj >= 1]
        s, j = min(((y, int(jj)) for y, jj in cands), key=lambda z: (F(n * z[1] - 1) / rho[z[0]], -z[0]))
    best = None
    for y in range(m):
        k = max(1, math.ceil((Rs * rho[y] + 1) / n))
        while F(n * k - 1) / rho[y] < Rs: k += 1
        while k > 1 and F(n * (k - 1) - 1) / rho[y] >= Rs: k -= 1
        e = F(n * k - 1) / rho[y]
        if best is None or e < best[0] or (e == best[0] and y < best[1]): best = (e, y)
    width = best[0] - Rs; c = best[1]
    strip = s is not None and abs(rho[s] - n * round(rho[s] / n)) < 1 and round(rho[s] / n) >= 1
    if nm == 0: k_ = "K0z" if width == 0 else "K0"
    elif width == 0: k_ = "K1z" if nm == 1 else "K2z"
    elif c == s: k_ = ("K1s" if nm == 1 else "K2s") + ("1" if j == 1 else "2")
    elif nm == 1: k_ = "K1a" if j == 1 else "K1b"
    elif j == 1: k_ = "K2a" if strip else "K2c"
    else: k_ = "K2b" if strip else "K2d"
    return k_, (s + 1 if s is not None else 0, c + 1), nm, Rs
H = {3: 200, 4: 90, 5: 50, 6: 30, 7: 22}
for n in range(3, 8):
    cnt = Counter(); pairs = set(); mx = 0; Rmax = F(0); N = 0
    for S in combinations(range(1, H[n] + 1), n - 1):
        if math.gcd(*S) != 1: continue
        k, p, nm, Rs = taxo(S, n); cnt[k] += 1; pairs.add(p); mx = max(mx, nm); Rmax = max(Rmax, Rs); N += 1
    real = [c for c in CLASSES if cnt[c]]
    print(f"n={n} (H={H[n]}, {N} sets): {len(real)} classes realised; empty: {[c for c in CLASSES if not cnt[c]]}")
    print("   " + ", ".join(f"{c} {cnt[c]}" for c in real))
    nonzero = sorted(p for p in pairs if p[0])
    print(f"   (opener rank, closer rank) pairs with a move: {len(nonzero)} of {(n-1)*(n-1)}; most moves {mx}; largest R* {Rmax} (~{float(Rmax):.3f})")
