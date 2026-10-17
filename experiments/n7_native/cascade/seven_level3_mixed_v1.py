#!/usr/bin/env python3
"""Exhaustive: four units mod 343 (scaled so u1 = 1) plus one valuation-1 multiple 7 d' (d' a unit mod 49) are lonely on
the level-3 unit grid: some unit k mod 343 with every u k mod 343 in [49, 294] and d' k mod 49 in [7, 42].  EXACT.
(The valuation-2 multiple is automatic at level 3.)"""
import numpy as np, time
N = 343
units = [u for u in range(1, N) if u % 7]
G = np.array([[1 if 49 <= (u * k) % N <= 294 else 0 for k in units] for u in units], dtype=np.int32)
dps = [d for d in range(1, 49) if d % 7]
H = np.array([[1 if 7 <= (d * k) % 49 <= 42 else 0 for k in units] for d in dps], dtype=np.int32)
t0 = time.time(); fails = []
for i in range(len(units)):
    for j in range(i, len(units)):
        m = G[0] * G[i] * G[j]
        C = (G * m) @ H.T          # C[u4, d'] = sum_k G[u4,k] m[k] H[d',k]
        z = np.argwhere(C == 0)
        for a, b in z[:3]: fails.append((1, units[i], units[j], units[a], dps[b]))
print(f"failing (1,u2,u3,u4 mod 343; d' mod 49): {len(fails)}; first {fails[:10]}; {time.time() - t0:.0f} s")
