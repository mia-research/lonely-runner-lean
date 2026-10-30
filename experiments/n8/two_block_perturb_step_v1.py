"""E653 perturbation (rule 12). Part A: the two moves where the derived rule and the cascade differ; print every
in-way candidate's exit (tie check). Part B: two families with different steps; move ONE other-block runner at a time
by -1/24 and +1/24 (that block is then no longer an AP) and print, per move, delta = s t, frac(dj*delta) and the step.
Cascade unchanged. Exact Fractions."""
import math
from fractions import Fraction as F
E = F(1, 8)
def frac(x): return x - math.floor(x)
def dist(x):
    f = frac(x); return min(f, 1 - f)
def run(v, k):
    rd = sorted((abs(x - v[k]), i) for i, x in enumerate(v) if i != k)
    r = [d for d, _ in rd]; who = [i for _, i in rd]
    t = F(1, 8 * r[0]); out = []
    while True:
        way = [(i, d) for i, d in enumerate(r) if dist(d * t) < E]
        if not way: return t, out
        exits = sorted((((round(d * t) + E) / d), who[i]) for i, d in way)
        best = None
        for i, d in way:
            M = round(d * t); nt = (F(M) + E) / d
            if best is None or nt > best[0]: best = (nt, who[i], M)
        out.append((t, exits, best[1:])); t = best[0]
def sp(p, A, b): return [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
print("Part A")
for (p, b, G, k) in [(2, F(7, 4), F(119, 8), 1), (6, F(7, 12), F(17, 2), 6)]:
    t, out = run(sp(p, G + p - 1, b), k)
    for (tt, ex, st) in out: print("  state", tt, "in-way exits", [(str(e), w) for e, w in ex], "-> setter", st)
print("Part B")
for (p, b, G, k) in [(2, F(5, 12), F(4), 0), (4, F(7, 3), F(3), 0)]:
    base = sp(p, G + p - 1, b)
    for mover in [None] + list(range(p, 8)):
        for dv in ([F(0)] if mover is None else [F(-1, 24), F(1, 24)]):
            v = list(base)
            if mover is not None: v[mover] += dv
            t, out = run(v, k)
            steps = [(w, M) for (_, _, (w, M)) in out]
            print("  p=%d b=%s G=%s k=%d mover=%s dv=%s landing R=%s setters(runner,lap)=%s" % (p, b, G, k, mover, dv, 8 * t, steps))
