"""WP3 item 1 continued.  (a) The longest blocked stretch of the extremal block [165,166,337,494,505,772]: where it is,
and which runners' zones chain to form it.  (b) Resolution: the block scaled by 5 and 20 and re-climbed with fine
steps -- does Q = L * min(minF, sigma5) keep rising?  (c) Structured family: pairs at progression positions,
{a, a+p, 2a+q, 3a, 3a+r, 4.7a}, pair offsets varied.  Exact."""
from fractions import Fraction as F
from block_extremal_v1 import comps, Q, climb
B = [165, 166, 337, 494, 505, 772]
cs = comps(B); L, a0, b0 = max(((b - a, a, b) for a, b in cs if a > 0))
print(f"(a) extremal block {B}: longest blocked stretch [{a0}, {b0}] = [{float(a0):.5f}, {float(b0):.5f}], length {L} = {float(L*165):.4f} laps of 165")
chain = []
for d in B:
    for m in range(0, d + 2):
        za, zb = F(8 * m - 1, 8 * d), F(8 * m + 1, 8 * d)
        if zb > a0 and za < b0: chain.append((za, zb, d, m))
chain.sort()
print("    zones inside it (start, end, runner, lap):")
for za, zb, d, m in chain: print(f"      [{float(za):.5f}, {float(zb):.5f}]  runner {d} lap {m}")
print("    positions (laps mod 1) of each runner at the stretch's midpoint:", [round(float((d * (a0 + b0) / 2) % 1), 3) for d in B])
print("(b) resolution: scale and re-climb")
for k in (5, 20):
    start = [k * x for x in B]
    _, cur, qq, q0 = climb(start)
    print(f"    x{k}: start Q {float(Q(start)[0]):.4f} -> climbed Q {qq} ({float(qq):.4f}) block {cur} shape {[round(x / cur[0], 4) for x in cur]}")
print("(c) pairs at progression positions: a = 200, block {a, a+p, 2a+q, 3a, 3a+r, s}")
best = None
for p in (1, 2, 4, 8, 16):
    for r in (1, 4, 11, 20):
        for q in (-3, 0, 7):
            for s in (900, 936, 950):
                blk = [200, 200 + p, 400 + q, 600, 600 + r, s]
                qq = Q(blk)[0]
                if best is None or qq > best[0]: best = (qq, blk)
print(f"    best in the structured family: Q = {best[0]} ({float(best[0]):.4f}) block {best[1]}")
