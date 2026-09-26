"""Read the cascade move by move on the manuscript's 28-move case (sec 6.10): arrangement
(27,70,107,137,159,188,344,393), runner 393.  At each instant t (scale D = 1/(8t)): every other runner's position in
eighths mod 8 (signed differences), who is in the way (within 1 of a multiple of 8), the setter x and its lap N, the
setter's shortfall g = (8N+1) - s_x (how far below its landing slot it sat), and each runner's advance in eighths over
the move, which is g * d_y/d_x (sec 6.2, a step is one dilation).  Exact."""
from fractions import Fraction as F
from math import floor
def nd(x): x = x % 1; return min(x, 1 - x)
V = [27, 70, 107, 137, 159, 188, 344, 393]; k = 7
ds = [v - V[k] for j, v in enumerate(V) if j != k]
t = F(1, 8 * min(abs(d) for d in ds)); step = 0
fmt = lambda x: f"{float(x):6.2f}"
print("differences:", ds)
while True:
    pos = [(8 * d * t) % 8 for d in ds]
    way = [i for i, d in enumerate(ds) if nd(d * t) < F(1, 8)]
    print(f"move {step:2d}  t={float(t):.6f}  eighths: " + " ".join(fmt(p) + ("*" if i in way else " ") for i, p in enumerate(pos)))
    if not way: print("  CLEAR: nobody within 1 of a multiple of 8"); break
    best = None
    for i in way:
        a = abs(ds[i]); N = floor(a * t - F(1, 8)) + 1; o = (N + F(1, 8)) / a
        if best is None or o > best[0]: best = (o, i, N)
    o, x, N = best
    s_x = 8 * abs(ds[x]) * t; g = (8 * N + 1) - s_x
    adv = [8 * abs(d) * (o - t) for d in ds]
    print(f"          setter diff {ds[x]} lap {N}: sat at {float(s_x):.3f}, lands on {8*N+1}; shortfall g = {float(g):.3f}; "
          f"advances: " + " ".join(fmt(a) for a in adv))
    t = o; step += 1
