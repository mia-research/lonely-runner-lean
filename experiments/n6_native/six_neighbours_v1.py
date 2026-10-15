#!/usr/bin/env python3
"""E31: why a box L and its neighbour B = L +- e_r (runner r one lap on or back) stand together, at the lineage
deaths of six_lineage_v1.tsv where the takeover is such a neighbour. Speeds at the death x (runners above the mover
at S, below at the grid, mover at x). For the four runners other than r, J = the intersection of their bands at
L's laps (shared by L and B). Runner r is in the way between consecutive bands: its blocked window between lap k and
k+1 is [(k + 5/6)/d_r, (k + 1 + 1/6)/d_r]. Records:
  - whether J contains r's blocked window with both of r's bands meeting J (so J is cut by r into two pieces, L's
    piece and B's piece);
  - J's length in laps of r (d_r * |J|), and in laps of the mover;
  - r's role (mover, slower than mover, faster), and r's rank;
  - which runners bound J (latest entry, earliest exit), by role;
  - the readings of the four others at the middle of r's blocked window (the cut).
Usage: six_neighbours_v1.py file.tsv"""
import sys, ast
from fractions import Fraction as F
from collections import Counter
rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])][1:]
def frac(z): return z - (z.numerator // z.denominator)
c = Counter(); rrole = Counter(); Jr = Counter(); Jm = Counter(); bounds = Counter(); rrank = Counter(); n = 0
cutslack = Counter(); ex = []
for row in rows:
    if not row[0].startswith("ordinary") and not row[0].startswith("chain"): continue
    d = ast.literal_eval(row[6]); nz = [(i + 1, v) for i, v in enumerate(d) if v]
    if len(nz) != 1 or abs(nz[0][1]) != 1: continue
    r, s = nz[0]; n += 1
    S = ast.literal_eval(row[0][row[0].index("("):]); m = int(row[1]); x = F(row[2]); L = ast.literal_eval(row[3])
    W = [F(S[i]) if i + 1 > m else F(S[0] * (i + 1)) for i in range(5)]; W[m - 1] = x
    others = [i for i in range(1, 6) if i != r]
    ent = {i: (6 * L[i-1] + 1) / (6 * W[i-1]) for i in others}; ext = {i: (6 * L[i-1] + 5) / (6 * W[i-1]) for i in others}
    J0, J1 = max(ent.values()), min(ext.values())
    k = min(L[r-1], L[r-1] + s); dr = W[r-1]
    b0, b1 = (6 * k + 5) / (6 * dr), (6 * k + 7) / (6 * dr)           # r blocked between its lap k and lap k+1
    band_k = ((6 * k + 1) / (6 * dr), b0); band_k1 = (b1, (6 * k + 11) / (6 * dr))
    cut = J0 < b0 and b1 < J1          # both pieces have positive length inside J
    meets = J0 <= b0 and b1 <= J1
    c["J cut by r's blocked window, both pieces open" if cut else ("touching (a piece of length 0)" if meets else "other")] += 1
    role = "mover" if r == m else ("slower than mover" if r < m else "faster than mover")
    rrole[role] += 1; rrank[r] += 1
    Jr[min(round(float((J1 - J0) * dr), 1), 3.0)] += 1
    Jm[min(round(float((J1 - J0) * x), 2), 1.0)] += 1
    def rl(i): return "mover" if i == m else ("slower" if i < m else "faster")
    lo = [i for i in others if ent[i] == J0][0]; hi = [i for i in others if ext[i] == J1][0]
    bounds[(rl(lo), rl(hi))] += 1
    tc = (b0 + b1) / 2
    sl = min(min(frac(W[i-1] * tc) - F(1, 6), F(5, 6) - frac(W[i-1] * tc)) for i in others)
    cutslack[round(float(sl), 2)] += 1
    if not cut and len(ex) < 5: ex.append((S, m, str(x), L, r, s, float(J0), float(J1), float(b0), float(b1)))
print(f"neighbour takeovers (one runner +-1 lap): {n}")
print("  structure:", dict(c))
print("  r's role:", dict(rrole), "; r's rank:", dict(sorted(rrank.items())))
print("  |J| in laps of r (3.0 = 3+):", dict(sorted(Jr.items())))
print("  |J| in laps of the mover (1.0 = 1+):", dict(sorted(Jm.items())[:12]), "...")
print("  J bounded by (latest entry, earliest exit) roles:", dict(bounds.most_common()))
print("  least slack of the four others at the middle of the cut:", dict(sorted(cutslack.items())[:10]), "...")
for e in ex: print("  not cut:", e)
