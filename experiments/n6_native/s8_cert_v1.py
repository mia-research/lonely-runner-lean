#!/usr/bin/env python3
"""Exact cell-subdivision certificate for §8 (v3 <= 3 v1), in ratios x_i = v_i/v_1 (x_1 = 1).
Domain D: 1 <= x2 <= x3 <= 3, x3 <= x4 <= x5. Part of D with x4 >= 6 is closed by the first window (W3 (0,0,0), uniform
form: 4 x3 <= x4 (5 - x3), true for x3 <= 3, x4 >= 6). The rest is the bounded box x2, x3 in [1,3], x4 in [1,6], with
x5 in [1, X] or in [X, inf). Statements (all instances of proved lemmas, conditions in closed form):
  W3 laps m (m1,m2,m3): U - L >= 1/(3 x4) + 2/(3 x5), L = max (m_i + 1/6)/x_i, U = min (m_i + 5/6)/x_i, i = 1..3
       (closed form of window_two: the residue condition holds when the window is at least 1/(3a) + 2/(3b));
  F4 laps (m1..m4): U - L >= 1/(3 x5) over runners 1..4;
  BOX k: (6 k_i + 1) x_j <= (6 k_j + 5) x_i for all i != j.
A cell (product of intervals, clipped by the ordering) is certified when one statement holds at its worst corner
(each condition is monotone in each variable, so the worst corner is exact). Otherwise bisect the widest side.
Output: cells certified per statement, failing cells at the depth limit (listed), and the depth reached."""
import sys
from fractions import Fraction as F
from collections import Counter
INF = None
X = F(int(sys.argv[1]) if len(sys.argv) > 1 else 30)
MAXD = int(sys.argv[2]) if len(sys.argv) > 2 else 40
W3 = [(0, 0, 0), (1, 2, 3), (0, 1, 1), (0, 0, 1)]
F4 = [(0, 0, 0, 0)]
BX = [(0,0,0,0,0), (0,0,0,0,1), (0,0,0,1,1), (0,0,1,1,2), (0,1,2,3,4),
      (0,0,0,1,2), (0,1,2,3,8), (1,3,4,5,7), (1,2,3,4,6), (0,1,1,2,2), (1,3,4,6,8)]
EXTRA = []
def clip(c):
    (a2, b2), (a3, b3), (a4, b4), (a5, b5) = c
    a2 = max(a2, F(1)); b3 = min(b3, F(3))
    a3 = max(a3, a2); a4 = max(a4, a3); a5 = max(a5, a4)
    b4 = min(b4, b5) if b5 is not None else b4
    b3 = min(b3, b4); b2 = min(b2, b3)
    if a2 > b2 or a3 > b3 or a4 > b4 or (b5 is not None and a5 > b5): return None
    return ((a2, b2), (a3, b3), (a4, b4), (a5, b5))
def lo(c, i): return F(1) if i == 0 else c[i - 1][0]
def hi(c, i): return F(1) if i == 0 else c[i - 1][1]
def ok_w3(c, m):
    U = min(F(6 * m[i] + 5, 6) / hi(c, i) for i in range(3)); L = max(F(6 * m[i] + 1, 6) / lo(c, i) for i in range(3))
    return U - L >= F(1, 3) / lo(c, 3) + F(2, 3) / lo(c, 4)
def ok_f4(c, m):
    if c[2][1] is None: return False
    U = min(F(6 * m[i] + 5, 6) / hi(c, i) for i in range(4)); L = max(F(6 * m[i] + 1, 6) / lo(c, i) for i in range(4))
    return U - L >= F(1, 3) / lo(c, 4)
def ok_box(c, k):
    if c[3][1] is None: return False
    return all((6 * k[i] + 1) * hi(c, j) <= (6 * k[j] + 5) * lo(c, i) for i in range(5) for j in range(5) if i != j)
def certify(c):
    for m in W3:
        if ok_w3(c, m): return ("W3", m)
    for m in F4:
        if ok_f4(c, m): return ("F4", m)
    for k in BX + EXTRA:
        if ok_box(c, k): return ("BOX", k)
    return None
used = Counter(); fails = []; maxd = 0; ncell = 0
def run(c, d):
    global maxd, ncell
    c = clip(c)
    if c is None: return
    ncell += 1; maxd = max(maxd, d)
    r = certify(c)
    if r: used[r] += 1; return
    if d >= MAXD: fails.append(c); return
    widths = [(c[i][1] - c[i][0]) if c[i][1] is not None else F(-1) for i in range(4)]
    i = max(range(4), key=lambda j: widths[j])
    a, b = c[i]; mid = (a + b) / 2
    run(c[:i] + ((a, mid),) + c[i + 1:], d + 1); run(c[:i] + ((mid, b),) + c[i + 1:], d + 1)
start_cells = [((F(1), F(3)), (F(1), F(3)), (F(1), F(6)), (F(1), X)), ((F(1), F(3)), (F(1), F(3)), (F(1), F(6)), (X, None))]
for c in start_cells: run(c, 0)
print(f"X={X}, depth limit {MAXD}: cells visited {ncell}, certified {sum(used.values())}, failing {len(fails)}, max depth {maxd}")
for k, n in used.most_common(): print(f"   {n:7d}  {k}")
for c in fails[:20]: print("   FAIL", [(str(a), str(b)) for a, b in c])
