#!/usr/bin/env python3
"""§5 k = 1 near the tight set (1,3,4,5,9): integer sets (v1, v2, v1+v2, v4, v5) with ratios within 6% of (1,3,4,5,9),
v1 <= 20; floats. Exact best gap  g = max_t min_i ||v_i t||  (over t in [0,1], from the breakpoints of the piecewise-linear
min: candidate t where two runners' distances are equal), and the excess g - 1/6 against the ratio distance."""
import math
from fractions import Fraction as F
def best_gap(vs):
    """floats: the max of min_i ||v_i t|| is attained where two runners' distances cross: t = k/(vi + vj) or k/(vj - vi)."""
    best = 0.0; bt = None
    for i in range(len(vs)):
        for j in range(i + 1, len(vs)):
            for s in (vs[i] + vs[j], vs[j] - vs[i]):
                if s <= 0: continue
                for k in range(s + 1):
                    t = k / s
                    g = min(abs(v * t - round(v * t)) for v in vs)
                    if g > best: best, bt = g, t
    return best, bt
tgt = (1, 3, 4, 5, 9); rows = []
for v1 in range(1, 21):
    for v2 in range(int(2.82 * v1), int(3.18 * v1) + 1):
        v3 = v1 + v2
        for v4 in range(max(v3 + 1, int(4.7 * v1)), int(5.3 * v1) + 1):
            for v5 in range(max(v4 + 1, int(8.46 * v1)), int(9.54 * v1) + 1):
                S = (v1, v2, v3, v4, v5)
                if math.gcd(*S) != 1: continue
                g, t = best_gap(S)
                d = max(abs(S[i] / v1 - tgt[i]) / tgt[i] for i in range(5))
                rows.append((d, g - 1 / 6, S, round(t, 5)))
rows.sort()
print("ratio distance, best gap - 1/6, set, t:")
for r in rows[:25]: print("  %.4f  %.5f  %s  t=%s" % r)
print("smallest excess among sets with distance > 0:", min((r for r in rows if r[0] > 0), key=lambda r: r[1]))
