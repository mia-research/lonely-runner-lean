#!/usr/bin/env python3
"""Exact cell certificate for §8, v4: v3's tests, with the box list extended in rounds. After each round, every failing
cell's centre is examined: its lonely lap vectors with t <= 3/v1 (exact), and the box of largest width there is added
to the list; three-block windows on the first three laps of those boxes are added too. Rounds stop when no cell fails
or nothing new is added. Usage: X depth rounds. Writes the final list and the certified-cell tree size."""
import sys, math
from fractions import Fraction as F
from collections import Counter
exec(open("s8_cert_v3.py").read().split("exec(\"start_cells = []\"")[0])
ROUNDS = int(sys.argv[3]) if len(sys.argv) > 3 else 6
def lonely_boxes(x, tmax):
    pts = sorted(set([F(6 * k + j, 6) / d for d in x for k in range(int(tmax * d) + 1) for j in (1, 5)]))
    out = {}
    for a in pts:
        if a <= tmax and all(F(1, 6) <= (d * a) % 1 <= F(5, 6) for d in x):
            k = tuple((d * a).numerator // (d * a).denominator for d in x)
            U = min(F(6 * kk + 5, 6) / d for kk, d in zip(k, x)); out[k] = max(out.get(k, F(-1)), U - a)
    return out
def starts():
    cs = []
    for a2 in (1, 2):
        for a3 in (1, 2):
            for a4 in range(1, 6):
                for a5 in range(1, int(X)):
                    cs.append(((F(a2), F(a2 + 1)), (F(a3), F(a3 + 1)), (F(a4), F(a4 + 1)), (F(a5), F(a5 + 1))))
                cs.append(((F(a2), F(a2 + 1)), (F(a3), F(a3 + 1)), (F(a4), F(a4 + 1)), (X, None)))
    return cs
for rnd in range(ROUNDS + 1):
    used.clear(); fails.clear(); ncell = 0; maxd = 0
    for c in starts(): run(c, 0)
    print(f"round {rnd}: cells {ncell}, certified {sum(used.values())}, failing {len(fails)}, |W3| {len(W3)}, |BX| {len(BX) + len(EXTRA)}")
    if not fails or rnd == ROUNDS: break
    new = 0
    for c in fails:
        if c[3][1] is None: continue
        x = [F(1)] + [(a + b) / 2 for a, b in c]
        bx = lonely_boxes(x, F(3))
        if not bx: continue
        k = max(bx, key=lambda z: bx[z])
        if k not in BX and k not in EXTRA: EXTRA.append(k); new += 1
        if k[:3] not in W3: W3.append(k[:3]); new += 1
    if not new: break
print("final windows W3:", W3)
print("final boxes:", BX + EXTRA)
for k, n in used.most_common(): print(f"   {n:7d}  {k}")
for c in fails[:10]: print("   FAIL", [(str(a), str(b) if b is not None else 'inf') for a, b in c])
