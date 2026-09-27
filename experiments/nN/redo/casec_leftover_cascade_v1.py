"""E157: the 15 sets no grid-class reference (m <= 8) covers, through the cascade: landing R* (units of d_min), chain
(rank, lap, R), residues of each reading mod 8 d_min (captures), and the landing laps."""
import ast
from fractions import Fraction as F
from math import floor
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def chain(T):
    t = F(1, 8 * T[0]); mv = []
    while True:
        W = [d for d in T if nd(d * t) < E8]
        if not W: return t, mv
        ex = {d: (F(floor(d * t - E8) + 1) + E8) / d for d in W}
        t2 = max(ex.values()); a = max(W, key=lambda d: ex[d]); mv.append((T.index(a), floor(a * t2), round(float(8 * T[0] * t2), 5))); t = t2
line = [l for l in open('casec_gridclass_v1.out') if l.startswith('P2')][0]
U = ast.literal_eval(line.split('uncovered (m<=8): ')[1].split(' ', 1)[1])
for T in U:
    t, mv = chain(T); m = T[0]
    res = [(d % (8 * m)) / m for d in T]
    print(T, "R* = %.5f" % float(8 * m * t), "res mod 8m (/m):", [str(F(r)) for r in res])
    print("    chain:", mv)
