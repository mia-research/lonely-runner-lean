#!/usr/bin/env python3
"""The plane v4 = 5 v1 through the tight set. (A) a = 0 (v2 = 3 v1): (c, 3c, 4c, 5c, 9c + d5): earliest lonely T = v1 t
against e = d5/c, and the product |e| T (drift: runner 5 must move from its reading at the (1,3,4,5)-windows to its band).
(B) e = 0, a != 0: (c, 3c + d2, 4c + d2, 5c, 9c + 2 d2... ) i.e. v5 = v3 + v4: earliest T against a = d2/c.
The (1,3,4,5) windows: T in [n + 13/30, n + 11/24] and mirror, where 9T mod 1 lies in [0.9, 0.125]."""
import math
from s5k1_tight_v2 import lonely
print("(A) a = 0, b = 0, e = d5/c:")
for c in (6, 10, 20, 40, 80, 160):
    for d5 in (-1, 1, -3, 3):
        S = (c, 3 * c, 4 * c, 5 * c, 9 * c + d5)
        if math.gcd(*S) != 1: continue
        iv = lonely(S); T = iv[0][0] * c if iv else None
        print(f"   c {c:4d} d5 {d5:+d}: e = {d5 / c:+.4f}, earliest T = {T:.4f}, |e| T = {abs(d5 / c) * T:.4f}, window length (T) {(iv[0][1] - iv[0][0]) * c:.5f}")
print("(B) b = 0, e = 0 (v5 = v3 + v4), a = d2/c:")
for c in (6, 10, 20, 40, 80, 160):
    for d2 in (-1, 1, -2, 2):
        S = (c, 3 * c + d2, 4 * c + d2, 5 * c, 9 * c + d2)
        if math.gcd(*S) != 1 or not all(S[i] < S[i + 1] for i in range(4)): continue
        iv = lonely(S); T = iv[0][0] * c if iv else None
        print(f"   c {c:4d} d2 {d2:+d}: a = {d2 / c:+.4f}, earliest T = {T:.4f}, |a| T = {abs(d2 / c) * T:.4f}, window length (T) {(iv[0][1] - iv[0][0]) * c:.5f}")
