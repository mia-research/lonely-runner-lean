"""E154: the six-reading groups through the CASCADE.  A slow runner (the nearest runner alone, reading 1/A in the group's
units: blocks A.[8k+1, 8k+7]) below a six-reading group G (least = 1).  Run the full cascade on {1/A} u G from its bound
(R_G = A) and read the chain: the setters (group reading rank, lap) of every move, which block of the slow runner the
landing is in, and -- when the landing is past the first block -- the moves that carry it across the slow runner's
window (7A, 9A): who sets them (the slow runner itself, a crowd sweep, or a bridge).  Starts A: the worst candidates
(ends of G's first lonely block and a grid of starts in [1.7, 12]).  Shapes: the E153 extremal fine shapes and integer
six-sets with least <= 3.  Exact.  Protections: progress file, caffeinate by the caller, the verified control first."""
import itertools, sys
from fractions import Fraction as F
from math import floor
from collections import Counter
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
from six_blocks_v2 import control
E8 = F(1, 8); PROG = 'six_blocks_cascade_v1.progress'
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def chain(T):
    """cascade on readings T (any units) from the bound of the least; returns landing t and moves (reading, lap, t)"""
    t = F(1, 8 * min(T)); mv = []
    while True:
        W = [d for d in T if nd(d * t) < E8]
        if not W: return t, mv
        ex = {d: (F(floor(d * t - E8) + 1) + E8) / d for d in W}
        t2 = max(ex.values()); a = max(W, key=lambda d: ex[d]); mv.append((a, floor(a * t2), t2)); t = t2
def read(G, A):
    slow = 1 / A; T = [slow] + list(G)
    t, mv = chain(T)
    Rs = 8 * slow * t                       # the slow runner's R (its own units): blocks [8k+1, 8k+7]
    blk = floor((Rs - 1) / 8)
    crossing = [m for m in mv if 8 * slow * m[2] > 7 and 8 * slow * m[2] <= 9 + 8 * blk]
    who = Counter('slow runner' if m[0] == slow else 'group rank %d lap %d' % (sorted(G).index(m[0]), m[1]) for m in crossing)
    return blk + 1, float(Rs), len(mv), who
if __name__ == '__main__':
    c, shape, R = control()
    open(PROG, 'a').write("positive control: %s blocks (expected 2)\n" % c)
    if c != 2: sys.exit("CONTROL FAILED")
    shapes = [(1.0, 1.3746, 1.7628, 2.2539, 2.5123, 3.23), (1.0, 1.3637, 1.7229, 2.2072, 2.4565, 3.1583),
              (1.0, 1.2781, 1.5849, 1.7644, 2.2574, 2.8117), (1.0, 1.2653, 1.4334, 1.5874, 1.7831, 2.2627)]
    out = Counter()
    for sh in shapes:
        G = [F(x).limit_denominator(10000) for x in sh]
        # starts: the end of G's first lonely block, just after it, and a grid
        L = clear_set(G, F(1), F(400)); b = L[0][1]
        starts = [b, b * F(1001, 1000)] + [F(k, 10) for k in range(17, 121, 4)]
        for A in starts:
            n, Rs, nmv, who = read(G, A)
            out[(n,)] += 1
            if n >= 2:
                line = "shape %s A=%.4f: lands in the slow runner's block %d at R=%.4f after %d moves; crossing (7,9) set by %s" % (sh, float(A), n, Rs, nmv, dict(who))
                print(line); open(PROG, 'a').write(line + "\n")
    print("blocks needed over these starts:", dict(out))
    open(PROG, 'a').write("ALLDONE\n")
