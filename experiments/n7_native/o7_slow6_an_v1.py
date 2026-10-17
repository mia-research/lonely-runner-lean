#!/usr/bin/env python3
"""Six-runner slow region (lonely instant at 1/7): coverage of the PROVABLE split mechanisms (EXACT Fractions,
formula-only).  For P = (v1..v6) and split j (1..5): slow block S = (v1..vj) has a window of length
W_j = 5/(7 v1) (j = 1) or 2 (1/(j+1) - 1/7)/v_j (native order j+1);  fast block F = (v_{j+1}..v6) needs GapProp with
window 0 and G <= W_j.  Gap bounds for F (window w):
  single u:             2/(7u) + 2w
  stretch recursion:    G(u + F') = 2/(7u) + 2 G(F')  if G(F') <= 5/(7u)
  union bound (|B|<=3): G = sum_B (4/(7d) + 2w) / (1/7 - w sum_B d)   if w sum_B d < 1/7   (w = 0: 4 sum 1/d < 5 sum 1/d,
                        Lean `gap_three`)
  block recursion:      F = B ++ F2 (B the slowest <= 3 runners): G(F) = union-bound gap of B with window G(F2)
Reports closure share on random slow-region samples and on structured families, and the unclosed shapes."""
import math, random, sys
from fractions import Fraction as Fr
from collections import Counter
from functools import lru_cache
@lru_cache(maxsize=None)
def G(F, w):
    """best provable gap (Fraction) for block F (tuple, ascending) with window w, or None"""
    best = None
    def upd(x):
        nonlocal best
        if x is not None and (best is None or x < best): best = x
    if len(F) == 1: upd(Fr(2, 7 * F[0]) + 2 * w)
    else:
        inner = G(F[1:], w)
        if inner is not None and inner <= Fr(5, 7 * F[0]): upd(Fr(2, 7 * F[0]) + 2 * inner)
    for k in range(1, min(3, len(F)) + 1):
        B, F2 = F[:k], F[k:]
        ww = w if not F2 else G(F2, w)
        if ww is None: continue
        s = ww * sum(B)
        if s < Fr(1, 7): upd(sum(Fr(4, 7 * d) + 2 * ww for d in B) / (Fr(1, 7) - s))
    return best
def W(P, j):
    return Fr(5, 7 * P[0]) if j == 1 else 2 * (Fr(1, j + 1) - Fr(1, 7)) / P[j - 1]
def closes(P):
    if P[5] >= 6 * P[4]: return 5
    for j in range(1, 6):
        g = G(tuple(P[j:]), Fr(0))
        if g is not None and g <= W(P, j): return j
    return 0
if __name__ == "__main__":
    rnd = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1); N = int(sys.argv[1])
    c = Counter(); bad = []
    while sum(c.values()) < N:
        v1 = rnd.randint(1, 30); v5 = rnd.randint(100 * v1 + 1, 100 * v1 + 20000); v6 = rnd.randint(v5 + 1, 6 * v5 - 1)
        P = (v1, *sorted(rnd.sample(range(v1 + 1, v5), 3)), v5, v6)
        if math.gcd(*P) != 1: continue
        j = closes(P); c[j] += 1
        if j == 0 and len(bad) < 3000: bad.append(P)
    n = sum(c.values())
    print(f"exact provable split mechanisms, {n} random six-runner sets with v5 > 100 v1, v6 < 6 v5: "
          f"closed {n - c[0]} ({(n - c[0]) / n:.2%}); by split {dict(sorted(c.items()))}")
    # shape of unclosed: largest consecutive ratio position and the size of the top bounded-ratio block
    shape = Counter()
    for P in bad:
        r = [Fr(P[i + 1], P[i]) for i in range(5)]
        jmax = max(range(5), key=lambda i: r[i]) + 1
        shape[(jmax, min(int(r[jmax - 1]), 50))] += 1
    print("   unclosed by (position of largest ratio j, floor of that ratio, capped 50):", sorted(shape.items())[:40])
    print("   examples:", bad[:12])
