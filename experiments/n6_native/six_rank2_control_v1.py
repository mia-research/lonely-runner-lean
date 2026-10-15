#!/usr/bin/env python3
"""Negative control for six_rank2_v1.py: witness(u, v) must be None when span(u, v) is only the circle of a tight u
(v = u, v = 2u, v = 0), and found for a non-tight integer u (sanity)."""
import sys
src = open("six_rank2_v1.py").read().split("for u in ((1, 2, 3, 4, 5)")[0]
sys.argv = ["x", "1", "24"]; ns = {}; exec(src, ns); witness = ns["witness"]
for u in ((1, 2, 3, 4, 5), (1, 3, 4, 5, 9)):
    for v in (u, tuple(2 * x for x in u), (0, 0, 0, 0, 0)):
        print(u, v, "witness:", witness(u, v))
print((1, 2, 3, 4, 6), (0,) * 5, "witness (non-tight u, expect found):", witness((1, 2, 3, 4, 6), (0,) * 5))
