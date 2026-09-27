"""E135: the doubled slot read from the cascade itself (no references, no lap search).  Walk the cascade from the bound
over every band set to 24.  At each move record the set W of readings in the subject's window (open zone, BSM); a move
with |W| >= 2 is two runners in the subject's slot at once.  The move goes to the latest exit (8k+1)/s of W; record, at
the new instant, where the other members of W sit (in eighths of a lap past their own leaving edge) and whether any
reading enters the window at the new instant (so the walk continues).  Exact."""
import itertools
from fractions import Fraction as F
from math import floor
from collections import Counter
E8 = F(1, 8)
def pos8(d, t):  # position in eighths of a lap, in [0, 8)
    return (8 * d * t) % 8
def in_way(d, t):
    p = pos8(d, t); return p < 1 or p > 7
def trace(T):
    t = F(1, 8 * T[0]); moves = []
    while True:
        W = [d for d in T if in_way(d, t)]
        if not W: return 8 * T[0] * t, moves
        exits = {d: (F(floor(d * t - E8) + 1) + E8) / d for d in W}
        t2 = max(exits.values()); setter = max(W, key=lambda d: exits[d])
        others = [pos8(d, t2) for d in W if d != setter]
        moves.append((len(W), setter, others, t2))
        t = t2
st = Counter(); lag = Counter(); after = Counter(); ex = []
for T in itertools.combinations(range(1, 25), 7):
    if not (7 * T[0] < T[-1] <= 9 * T[0]): continue
    R, mv = trace(T)
    for idx, (w, setter, others, t2) in enumerate(mv):
        st['moves with %d in the window' % w] += 1
        if w >= 2:
            for p in others: lag['other member at %s eighths past its edge' % ('<1' if p - 1 < 1 else '<2' if p - 1 < 2 else '>=2')] += 1
            after['moves left to the landing after a doubled move: %s' % min(len(mv) - idx - 1, 3)] += 1
            if len(ex) < 12 and w >= 3: ex.append((T, float(R), [(m[0], m[1], [round(float(x), 3) for x in m[2]], round(float(8 * T[0] * m[3]), 4)) for m in mv]))
for C in (st, lag, after):
    for k, v in sorted(C.items()): print("  %7d  %s" % (v, k))
print("\nexamples with three in the window at one move: T, R*, moves (in window, setter, others' positions in eighths, new R):")
for e in ex: print("  ", e)
