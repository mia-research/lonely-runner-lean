#!/usr/bin/env python3
"""Exhaustive: every 5-tuple of units mod 343 (up to a common unit scaling, so u1 = 1) is lonely on the level-3 unit grid:
some unit k mod 343 with every u k mod 343 in [49, 294].  EXACT (integer/boolean arithmetic).  For each pair (u2, u3)
with u2 <= u3, the matrix C[u4, u5] = #{k : good(1,k) good(u2,k) good(u3,k) good(u4,k) good(u5,k)} via one integer
matrix product; a zero entry is a failing tuple."""
import numpy as np, time
N = 343
units = np.array([u for u in range(1, N) if u % 7])
ks = units
G = np.array([[1 if 49 <= (u * k) % N <= 294 else 0 for k in ks] for u in units], dtype=np.int32)  # [u, k]
base = G[0]                     # u = 1
t0 = time.time(); fails = []; pairs = 0
for i in range(len(units)):
    for j in range(i, len(units)):
        m = base * G[i] * G[j]                 # k-mask for (1, u2, u3)
        if not m.any(): fails.append((1, units[i], units[j], None, None)); continue
        C = (G * m) @ G.T                      # C[u4, u5] = sum_k G[u4,k] m[k] G[u5,k]
        z = np.argwhere(C == 0)
        for a, b in z[:3]: fails.append((1, int(units[i]), int(units[j]), int(units[a]), int(units[b])))
        pairs += 1
print(f"pairs (u2 <= u3) checked: {pairs}; failing 5-tuples found: {len(fails)}; first: {fails[:10]}; {time.time() - t0:.0f} s")
