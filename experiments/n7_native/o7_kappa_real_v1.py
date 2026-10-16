#!/usr/bin/env python3
"""Phase 3a: kappa = v5 W5 for REAL speeds near the integer minimisers (1,3,4,5,7) and (1,4,5,6,7).
W5 over t in [0, T] with T = 60 (real speeds have no common period; T long enough for the near-integer windows to
recur), float band intersection. If kappa drops below 3/28 near these points, a real-ratio box certificate cannot
reach 3/28 there and integrality must enter, as in the order-six tight-point lemmas."""
import math, random
T = 60.0
def bands(v):
    out = []; m = 0
    while (m + 1 / 7) / v < T:
        out.append(((m + 1 / 7) / v, min((m + 6 / 7) / v, T))); m += 1
    return out
def W5(P):
    cur = bands(P[0])
    for v in P[1:]:
        B = bands(v); i = j = 0; out = []
        while i < len(cur) and j < len(B):
            lo, hi = max(cur[i][0], B[j][0]), min(cur[i][1], B[j][1])
            if hi > lo: out.append((lo, hi))
            if cur[i][1] < B[j][1]: i += 1
            else: j += 1
        cur = out
    return max((h - l for l, h in cur), default=0.0)
random.seed(1)
for base in [(1, 3, 4, 5, 7), (1, 4, 5, 6, 7), (1, 2, 3, 4, 5)]:
    print(f"{base}: integer kappa {base[4] * W5(base):.6f}")
    for eps in (1e-2, 3e-3, 1e-3):
        ks = []
        for _ in range(400):
            P = tuple(v * (1 + random.uniform(-eps, eps)) for v in base)
            ks.append((max(P) * W5(P), P))
        ks.sort()
        print(f"   eps {eps}: min kappa {ks[0][0]:.6f} at {tuple(round(x, 5) for x in ks[0][1])}; "
              f"share below 3/28 {sum(k < 3 / 28 - 1e-9 for k, _ in ks) / len(ks):.2%}")
