"""Proxy from offender_paths_v1/v2: when the bound grid is blocked, the isolation goes to the next opening of the runner
nearest the ENTERING edge (largest fractional reading at the bound, the one about to cross the subject's slot).
Tested as a named instant on every set of 7 distinct readings in 1..24 whose bound 1/(8 d_min) is not lonely.  Exact.

Recorded: is the edge runner's next opening lonely; does the cascade land there; for the exceptions, which runners
block the proxy instant, in which slot they sat at the bound (the oracle's view of why the proxy failed)."""
import itertools
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool

E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def lonely(T, t): return all(nd(d * t) >= E8 for d in T)
def cascade(T):
    t = F(1, 8 * T[0])
    while True:
        way = [d for d in T if nd(d * t) < E8]
        if not way: return t
        t = max((F(floor(d * t - E8) + 1) + E8) / d for d in way)
def next_opening(d, t):
    """least (N + 1/8)/d strictly after t"""
    N = floor(d * t - E8) + 1
    return (N + E8) / d
def slot(x): return int(floor(8 * (x % 1)))

def chunk(first):
    c = Counter(); blk = Counter(); ex = []
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest; t0 = F(1, 8 * T[0])
        if lonely(T, t0): continue
        c['bound blocked'] += 1
        fr = {d: (d * t0) % 1 for d in T}
        e = max(T, key=lambda d: (fr[d], d))
        te = next_opening(e, t0)
        ok = lonely(T, te); c['edge runner next opening lonely'] += ok
        ts = cascade(T); c['cascade lands there'] += (ts == te)
        c[('edge runner slot at bound', slot(e * t0))] += 1
        if not ok:
            B = [d for d in T if nd(d * te) < E8]
            for d in B: blk[('blocker slot at bound', slot(d * t0), 'blocker is a collider (slot 0)' if slot(d * t0) == 0 else '')] += 1
            blk[('number of blockers', len(B))] += 1
            if len(ex) < 6: ex.append((T, e, str(te), B, str(ts)))
    return c, blk, ex

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 19))
    c = Counter(); blk = Counter(); ex = []
    for a, b, x in parts: c.update(a); blk.update(b); ex += x
    for k, v in sorted(c.items(), key=str): print(k, v)
    print("exceptions: blockers of the proxy instant")
    for k, v in sorted(blk.items(), key=str): print("  ", k, v)
    print("examples (readings, edge runner, its next opening, blockers there, cascade t*):")
    for x in ex[:30]: print("  ", x)
