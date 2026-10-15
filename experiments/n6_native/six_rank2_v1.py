#!/usr/bin/env python3
"""E24: degenerate configurations of real rank >= 2.
A speed vector d of Q-rank r has orbit closure T = V + Z^5 (V the rational span, dim r). The orbit is dense in T,
so d has a positive-length lonely interval iff T meets the OPEN cube C° = (1/6,5/6)^5 mod 1; d is degenerate iff
T misses C° but the orbit touches the closed cube. Every all-nonzero integer vector w of the lattice V cap Z^5
lies in T with its own orbit; if T misses C°, every such w is not strictly lonely (tight, or a counterexample).
Part 1 (projection lemma check): u tight, v arbitrary in [-3,3]^5; claim: if v_l != 5 v_e (e = coordinate of the
  value 1, l = coordinate of 5 in u) then span(u,v) meets C° (direction y = alpha u + beta v with y_e > 0 > y_l
  moves the simple lonely point of u into C°). Witness = exact rational point (s,t) with s u + t v in C°.
Part 2: v_l = 5 v_e reduces to u and y with y_e = y_l = 0; all primitive y on the other three coordinates with
  |y| <= B: search a rational witness (s,t). Prints any y without a witness.
Usage: six_rank2_v1.py B Q"""
import sys, itertools, math
from fractions import Fraction as F
B, Q = int(sys.argv[1]), int(sys.argv[2])
def inside(x):
    f = x - math.floor(x); return F(1, 6) < f < F(5, 6)
grid = sorted({F(i, q) for q in range(1, Q + 1) for i in range(q)})
def witness(u, v):
    for s in grid:
        a = [s * x for x in u]
        rest = [i for i in range(5) if v[i] == 0]
        if not all(inside(a[i]) for i in rest): continue
        for t in grid:
            if all(inside(a[i] + t * v[i]) for i in range(5)): return (s, t)
    return None
for u in ((1, 2, 3, 4, 5), (1, 3, 4, 5, 9)):
    e, l = u.index(1), u.index(5)
    # Part 1
    n1 = miss1 = 0
    for v in itertools.product(range(-3, 4), repeat=5):
        if v[l] == 5 * v[e]: continue
        n1 += 1
        if witness(u, v) is None: miss1 += 1; print("  part1 no witness", u, v)
    mid = [i for i in range(5) if i not in (e, l)]
    n2 = 0; miss = []; seen = set()
    for yy in itertools.product(range(-B, B + 1), repeat=3):
        if not any(yy) or math.gcd(*yy) != 1: continue
        key = max(yy, tuple(-x for x in yy))
        if key in seen: continue
        seen.add(key); n2 += 1
        y = [0] * 5
        for i, c in zip(mid, yy): y[i] = c
        w = witness(u, y)
        if w is None: miss.append(yy)
    print(f"u = {u}: part 1 v with v_l != 5 v_e: {n1}, without witness {miss1}; "
          f"part 2 primitive y (|y| <= {B}, up to sign): {n2}, without witness {len(miss)} {miss[:20]}")
