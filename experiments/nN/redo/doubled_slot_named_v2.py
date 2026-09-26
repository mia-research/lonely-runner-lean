"""The named instants the Lean proof will use, checked exactly for every runner, every (s, r), m = 1..400.
  non-pair runner:  1/8
  home, interior s = 1..6, or (s, r) = (0, 7), (7, 0):  1/8 + 1/(64m)
  home, s = 0 (s = 7 mirrored, c -> 8 - c), c = r - s mod 8 in 1..6: t0 = (8N+1)/(8d) with
      c: 1 -> (2, 0), 2 -> (7, 3), 3 -> (7, 2), 4 -> (5, 1), 5 -> (6, 1), 6 -> (7, 1);
      t0 + 1/(64m) when the partner (difference 8m) reads a whole number of laps at t0
  far member (index r):  1/(8(8m + s - 7)), valid when 49 <= 48m + 6s; else (s = 0, m = 1) the listed instants.
Also prints, for the exceptional residue classes, the smallest margin of every reading from its band edge, which the
Lean proof needs (a reading at a/(8m) past a fixed position must stay inside the band for every m in the class)."""
from fractions import Fraction as F
def nd(x): x = x % 1; return min(x, 1 - x)
def lonely(v, k, t): return all(nd((v[i] - v[k]) * t) >= F(1, 8) for i in range(8) if i != k)
END = {1: (2, 0), 2: (7, 3), 3: (7, 2), 4: (5, 1), 5: (6, 1), 6: (7, 1)}
FAR01 = {1: F(9, 64), 2: F(9, 56), 3: F(3, 16), 4: F(9, 40), 5: F(17, 56), 6: F(25, 56), 7: F(1, 16)}
def t_for(s, r, m, k):
    if k not in (s, r): return F(1, 8)
    if k == r:
        if 49 <= 48 * m + 6 * s: return F(1, 8 * (8 * m + s - 7))
        return FAR01.get(r)
    c = (r - s) % 8
    if 1 <= s <= 6 or (s, r) in ((0, 7), (7, 0)): return F(1, 8) + F(1, 64 * m)
    cc = c if s == 0 else 8 - c
    d, N = END[cc]; t0 = F(8 * N + 1, 8 * d)
    return t0 + F(1, 64 * m) if (8 * m * t0) % 1 == 0 else t0
bad = []
for s in range(8):
    for r in range(8):
        if r == s: continue
        for m in range(1, 401):
            v = [100 + i for i in range(8)]; v[r] = 100 + s + 8 * m
            for k in range(8):
                t = t_for(s, r, m, k)
                if t is None or not lonely(v, k, t): bad.append((s, r, m, k, t))
print(f"failures over every runner, every (s, r), m = 1..400: {len(bad)}", bad[:10])
