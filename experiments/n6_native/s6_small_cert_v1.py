#!/usr/bin/env python3
"""Certificate prototype for §6 with runner 1's orbit modulus E = D/g < 15 (coprime D < 15: g = 1; g | v4: the reduced
data). Class (E, l): at the meeting times runner 1 reads j/E and runner 4 reads l j/E (+ integers), j < E.
All closing conditions are upper bounds on M = v4/(3 v5), so every check is made at M = 1/3.
Parameters: U = v3/v2 = (c+1)/c, Q = v4/v3 = 1 + delta/((c+1)E), delta = (v4 - v3)/g >= dmin(E, l) (gcd(l,E), or E for l = 0),
near-runner Q (5 - U) < 4.
Leaves at M = 1/3:
  After(j,m):  1/6 <= j/E <= 5/9,  m + 1/6 <= l j/E + 5Q/6 - 1/3,       l j/E + QU/6 + 1/3 <= m + 5/6
  Before(j,m): 4/9 <= j/E <= 5/6,  m + 1/6 <= 1 - l j/E + 5Q/6 - 1/3,   1 - l j/E + QU/6 + 1/3 <= m + 5/6
  Sum(j) (only when delta = a', i.e. v4 = v3 + v1):  1/3 <= (j/E - 1/3) Q,  j/E <= (5/6)(2 - Q)   [close_sum at M = 1/3]
Part 1, c >= 5: a tree over boxes U in [1, 6/5], Q in [1, 4/(5-1)] per class, with
  Empty if 1 + dmin (1 - 1/u0)/E >= 4/(5 - u1)  (INT lower bound >= near-runner upper bound), or class-empty if 6E <= 19 dmin.
Part 2, c <= 4: every point (E, c, delta, a'), a' = v1/g < (c+1)E/3, gcd(a', E) = 1, delta near-runner: some leaf works."""
from fractions import Fraction as F
from math import gcd, floor, ceil
from collections import Counter
import sys
def leaves_box(E, l, u0, u1, q0, q1):
    M = F(1, 3)
    for j in range(E):
        p = F(j, E); x = F(l * j % E, E)   # runner-4 phase (mod 1); m absorbs integers
        if F(1, 6) <= p <= F(5, 9):
            lo = x + 5 * q0 / 6 - M - F(1, 6); hi = F(5, 6) - x - q1 * u1 / 6 - M
            m = ceil(lo - 1) if False else None
            # need integer m with m <= lo and m >= -hi ... i.e. m in [-hi, lo]
            mm = floor(lo)
            if mm >= -hi: return ("A", j, mm)
        if F(4, 9) <= p <= F(5, 6):
            y = (1 - x)
            lo = y + 5 * q0 / 6 - M - F(1, 6); hi = F(5, 6) - y - q1 * u1 / 6 - M
            mm = floor(lo)
            if mm >= -hi: return ("B", j, mm)
    return None
def dmin(E, l): return E if l % E == 0 else gcd(l, E)
def tree(E, l, u0, u1, q0, q1, depth, stats):
    d = dmin(E, l)
    if 1 + d * (1 - 1 / u0) / E >= 4 / (5 - u1): stats["empty"] += 1; return ("E",)
    q0e = max(q0, 1 + d * (1 - 1 / u0) / E); q1e = min(q1, 4 / (5 - u1))
    lf = leaves_box(E, l, u0, u1, q0e, q1e)
    if lf: stats["leaf"] += 1; return lf
    if depth > 40: stats["FAIL"] += 1; return ("FAIL", u0, u1, q0, q1)
    if (u1 - u0) * 4 > (q1 - q0):
        um = (u0 + u1) / 2; return ("SU", um, tree(E, l, u0, um, q0, q1, depth + 1, stats), tree(E, l, um, u1, q0, q1, depth + 1, stats))
    qm = (q0 + q1) / 2; return ("SQ", qm, tree(E, l, u0, u1, q0, qm, depth + 1, stats), tree(E, l, u0, u1, qm, q1, depth + 1, stats))
def size(t): return 1 if t[0] in "ABE" or t[0] == "FAIL" else 1 + size(t[2]) + size(t[3])
def fails(t):
    if t[0] == "FAIL": return [t]
    if t[0] in ("SU", "SQ"): return fails(t[2]) + fails(t[3])
    return []
tot = Counter(); bad = []
for E in range(2, 15):
    for l in range(E):
        d = dmin(E, l)
        if 6 * E <= 19 * d: tot["class empty (6E <= 19 dmin)"] += 1; continue
        st = Counter(); t = tree(E, l, F(1), F(6, 5), F(1), F(4, 3), 0, st)
        tot["classes with tree"] += 1; tot["nodes"] += size(t); tot["leaves"] += st["leaf"]; tot["empty leaves"] += st["empty"]
        if st["FAIL"]: bad.append((E, l, fails(t)[:2]))
print("Part 1 (c >= 5):", dict(tot)); print("  failures:", bad[:10])
# Part 2
res = Counter(); bad2 = []
for E in range(2, 15):
    for c in range(1, 5):
        U = F(c + 1, c); v3 = (c + 1) * E
        dl = 1
        while (1 + F(dl, v3)) * (5 - U) < 4:
            Q = 1 + F(dl, v3)
            for a in range(1, (v3 - 1) // 3 + 1):
                if gcd(a, E) != 1 or 3 * a >= v3 or a >= c * E: continue
                l = dl * pow(a, -1, E) % E if E > 1 else 0
                lf = leaves_box(E, l, U, U, Q, Q)
                if lf: res["region leaf"] += 1; continue
                if dl == a:
                    ok = any(F(1, 3) <= (F(j, E) - F(1, 3)) * Q and F(j, E) <= F(5, 6) * (2 - Q) for j in range(E))
                    if ok: res["sum"] += 1; continue
                res["OPEN"] += 1; bad2.append((E, c, dl, a, l))
            dl += 1
print("Part 2 (c <= 4) points:", dict(res)); print("  open:", bad2)
