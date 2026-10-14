"""How big is the order-8 word tree really? Breadth-first by length, with realisability pruning.

The word enumeration keeps only words whose LP has max tau > 0. This counts, level by level, how
many such words exist at a given ratio bound -- which decides whether the full certificate is
feasible if split into independent subtasks, or infeasible however it is split.

Also records the best R seen at each depth: since R = R_1 + sum (2 - n*delta)/s grows with every
move, the supremum lives at the LONGEST realisable words, so a depth-limited run is a LOWER bound
on sup R, never an upper bound.
"""
import os, sys, time
from fractions import Fraction as F
src = open(os.path.join(os.path.dirname(__file__), 'order_n_certificate_v1.py')).read().split("if __name__ ==")[0]
g = {'__name__': 'census'}
exec(src, g)
constraints = g['constraints']; opt = g['opt']; NV = g['NV']; n = g['n']
S = int(sys.argv[1]) if len(sys.argv) > 1 else 8
BUDGET = float(sys.argv[2]) if len(sys.argv) > 2 else 120.0
L = ((n - 1) * S - 1) // n
print(f"order {n}, ratio bound S = {S}, lap bound L = {L}, runners {NV}, cap R < {n-1}", flush=True)
print(f"time budget {BUDGET:.0f}s per level\n", flush=True)
level = [[(x, q)] for x in range(1, NV + 1) for q in range(1, L + 1)]
depth = 1
while level and depth <= NV * L:
    t0 = time.time(); keep = []; best = None; truncated = False
    for w in level:
        if time.time() - t0 > BUDGET: truncated = True; break
        cons = constraints(w)
        tau = opt(cons, NV, 'max', S, True)
        if tau is None or tau <= 0: continue
        keep.append(w)
        x, Q = w[-1]
        m = opt(cons, x - 1, 'min', S, False) if x > 0 else F(1)
        if m is not None and m > 0:
            R = F(n * Q + 1) / m
            if best is None or R > best: best = R
    print(f"  length {depth:2}: examined {len(level):8}  realisable {len(keep):8}  "
          f"best R {str(best) if best else '-':>10} = {float(best) if best else 0:.4f}"
          f"{'   [TRUNCATED by budget]' if truncated else ''}", flush=True)
    if truncated:
        print("  -> level not completed; the tree is too wide to enumerate at this depth", flush=True)
        break
    nxt = []
    for w in keep:
        used = {xx: qq for xx, qq in w}
        for nx in range(1, NV + 1):
            for nq in range(used.get(nx, 0) + 1, L + 1):
                nxt.append(w + [(nx, nq)])
    level = nxt; depth += 1
    if not level: print("  -> no further realisable words: the enumeration is COMPLETE", flush=True)
