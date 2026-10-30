"""E652. Perturb one two-block family through the exact cascade (rule 12): fixed p, b, subject k; G moves in steps
of 1/16 from 1/16 to Gcov. Printed per G: the landing as R_own = 8 u t, the setter (its block and its index j counted
from the reading nearest the subject in that block), its lap M, the moves, and the full (setter, lap) path.
Cascade copied unchanged from catalogue_by_outcome_v1.py. Exact Fractions."""
import math, sys
from fractions import Fraction as F
sys.path.insert(0, '.')
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from two_block_remainder_v1 import gcov
E = F(1, 8)
def dist(x):
    f = x - math.floor(x); return min(f, 1 - f)
def cascade_path(r):
    t = F(1, 8 * r[0]); path = []
    while True:
        way = [(i, d) for i, d in enumerate(r) if dist(d * t) < E]
        if not way: return t, path
        best = None
        for i, d in way:
            M = round(d * t); nt = (F(M) + E) / d
            if best is None or nt > best[0]: best = (nt, i, M)
        t, i, M = best; path.append((i, M))
p, b, k = int(sys.argv[1]), F(sys.argv[2]), int(sys.argv[3])
gc, _ = gcov(p, b)
v0 = lambda A: [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
own = range(p) if k < p else range(p, 8)
u = F(1) if k < p else b
print("p=%d b=%s subject=%d own step u=%s Gcov=%s" % (p, b, k, u, gc))
G = F(1, 16)
while G < gc:
    v = v0(G + p - 1)
    rd = sorted((abs(x - v[k]), i) for i, x in enumerate(v) if i != k)
    r = [d for d, _ in rd]; who = [i for _, i in rd]
    t, path = cascade_path(r)
    def lab(i):
        w = who[i]; blk = 'own' if w in own else 'oth'
        same = sorted((abs(v[x] - v[k]), x) for x in range(8) if x != k and ((x in own) == (blk == 'own')))
        j = [x for _, x in same].index(w)
        return '%s%d' % (blk, j)
    P = [(lab(i), M) for i, M in path]
    print("G=%-6s R_own=%-10s moves=%-2d landing-setter=%-12s path=%s" % (G, 8 * u * t, len(P), P[-1] if P else 'bound', P))
    G += F(1, 16)
