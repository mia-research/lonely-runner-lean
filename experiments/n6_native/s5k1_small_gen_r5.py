#!/usr/bin/env python3
"""(R5) 4-runner ivt intervals for the runner-5 sweep, a 1D tree in lam over [25/14, 16/5]: leaf (l0, l1, n1, m3, m4, pa, pb)
with pb - pa >= 1/(30 - l1) + 2/90 and term-wise 4-runner conditions (s5k1_small_gen_v2.leaf4_ok)."""
import math
from fractions import Fraction as F
exec(open("s5k1_small_gen_v2.py").read().split("A = greedy(")[0])
exec(open("s5k1_small_gen_v2.py").read().split("def findS(")[1].join(["", ""]) if False else "")
src = open("s5k1_small_gen_v2.py").read()
exec(src[src.index("def pair_ok("):src.index("nodes = 0")])
def find4(l0, l1):
    width = 1 / (30 - l1) + F(2, 90); lc = (l0 + l1) / 2
    for n1 in range(2):
        pa = n1 + F(1, 6)
        while pa + width <= n1 + F(5, 6):
            pb = pa + width; P = (pa + pb) / 2
            for yi in range(20, 101):
                y = F(yi, 120)
                m3 = math.floor(y + P - F(1, 6)); m4 = math.floor(y + lc * P - F(1, 6))
                if leaf4_ok(n1, m3, m4, pa, pb, (l0, l1)): return (n1, m3, m4, pa, pb)
            pa += width / 16
    return None
out = []
def rec(l0, l1, d):
    lf = find4(l0, l1)
    if lf: out.append((l0, l1) + lf); return
    if d > 20: raise SystemExit(f"R5 fail {float(l0)} {float(l1)}")
    m = (l0 + l1) / 2; rec(l0, m, d + 1); rec(m, l1, d + 1)
rec(F(25, 14), F(16, 5), 0)
print("R5 leaves:", len(out), [(float(a), float(b), n1, m3, m4, str(pa), str(pb)) for a, b, n1, m3, m4, pa, pb in out])
import pickle; pickle.dump(out, open("s5k1_small_r5.pkl", "wb"))
