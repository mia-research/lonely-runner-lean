#!/usr/bin/env python3
"""lam = 1 split. Near-runner gives delta = v4 - v3 < (c+1)D/(4c-1) < D, and lam = 1 gives delta = v1 mod D.
 c <= 2: v1 < v3/3 <= D, so delta = v1 (the sum relation, q4 = 1 + r1): usable = U union I, I = [1/3 + mu/q4, (5/6)(2 - q4)].
 c >= 3: U alone. Grid search for the smallest longest usable interval in each part."""
import math
exec(open("s6_diag_cont_v1.py").read().split("worst = {")[0])
w12 = (9, None); w3 = (9, None)
for c in list(range(1, 41)) + [100, 1000, 10**6]:
    qmax = 4 * c / (4 * c - 1)
    for i in range(0, 401):
        q4 = 1 + (qmax - 1) * i / 400
        lam4 = q4 * (5 / 6 - (c + 1) / (6 * c)); vs0 = q4 * (c + 1) / (6 * c); vs1 = 5 * q4 / 6
        for jj in range(1, 201):
            mu = (1 / 3) * jj / 200
            A = (1 / 6 - lam4 + mu - vs0, 5 / 6 - mu - vs0); Ap = (1 / 6 - lam4 + mu + vs1, 5 / 6 - mu + vs1)
            U = pre((1 / 6, 5 / 9), 1, A[0], A[1] - A[0]) + pre((4 / 9, 5 / 6), 1, Ap[0], Ap[1] - Ap[0])
            if c <= 2:
                lo, hi = 1 / 3 + mu / q4, 5 / 6 * (2 - q4)
                m = max(longest(U), hi - lo)
                if m < w12[0]: w12 = (m, (c, round(q4, 4), round(mu, 4)))
            else:
                m = longest(U)
                if m < w3[0]: w3 = (m, (c, round(q4, 4), round(mu, 4)))
print(f"lam 1, c <= 2 (sum relation): smallest of max(longest U, |I|) = {w12[0]:.4f} at {w12[1]}")
print(f"lam 1, c >= 3: smallest longest U = {w3[0]:.4f} at {w3[1]}   (1/15 = {1/15:.4f})")
