#!/usr/bin/env python3
"""Witnesses for the 10 points of s6_small_cert_v1 left open (all need the meeting fold). Reduced speeds
w = (a', cE, (c+1)E, (c+1)E + delta); at T = k/E with a' k = j (mod E): readings w1 T = N1 + j/E, w2 T, w3 T whole,
w4 T = N4 + (l j mod E)/E. A sub-window [sa, sb] of the window after (s > 0) or before (s < 0) the meeting time where
runner i reads in [m_i + 1/6, m_i + 5/6] at both ends (i = 1..4; for 2, 3 the phase is 0), and w4 (sb - sa) >= 1/3
(runner 5 folded alone, worst case v5 = v4)."""
from fractions import Fraction as F
from math import floor
pts = [(4, 1, 1, 1), (5, 1, 1, 1), (5, 1, 2, 2), (5, 1, 3, 3), (7, 1, 3, 2), (7, 1, 3, 3), (7, 3, 1, 8), (7, 3, 2, 9),
       (7, 4, 2, 9), (8, 2, 3, 3)]
def clear_ivs(p, w, L, U):
    """sub-intervals of [L, U] where p + w s is in some band [m+1/6, m+5/6]; returns (a, b, m)"""
    out = []
    lo, hi = p + w * L, p + w * U
    for m in range(floor(min(lo, hi)) - 1, floor(max(lo, hi)) + 2):
        a = (F(6 * m + 1, 6) - p) / w; b = (F(6 * m + 5, 6) - p) / w
        x, y = max(L, a), min(U, b)
        if x <= y: out.append((x, y, m))
    return out
for E, c, dl, a in pts:
    w = (a, c * E, (c + 1) * E, (c + 1) * E + dl); l = dl * pow(a, -1, E) % E
    found = None
    for j in range(E):
        p1, p4 = F(j, E), F(l * j % E, E)
        for side, (L, U) in (("after", (F(1, 6 * w[1]), F(5, 6 * w[2]))), ("before", (-F(5, 6 * w[2]), -F(1, 6 * w[1])))):
            for a1, b1, m1 in clear_ivs(p1, w[0], L, U):
                for a4, b4, m4 in clear_ivs(p4, w[3], a1, b1):
                    if w[3] * (b4 - a4) >= F(1, 3):
                        m2 = floor(w[1] * a4); m3 = floor(w[2] * a4)
                        found = (j, side, a4, b4, m1, m2, m3, m4); break
                if found: break
            if found: break
        if found: break
    print((E, c, dl, a), "l =", l, "->", found)
