"""Why the half lap: for the sets settled at q = 2 by ladder_nudge_v1 (readings <= 32), at the isolating instant
t = 1/2 + delta: (i) are the EVEN readings, on their own, isolated at the instant delta (each even e: circDist(e delta)
>= 1/8), i.e. is it the evens' own lower-order isolation?  (ii) where does delta sit against the evens' own bound
1/(8 e_min) (R1 for the evens: e_max <= 7 e_min)?  (iii) the odd readings: o delta against the half-way window.
Exact; tallies by exact situation."""
import itertools
from fractions import Fraction as F
from math import gcd
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import nd
from lemma_map_v1 import TESTS
from ladder_nudge_v1 import ladder_nudge

def chunk(first):
    c = Counter(); ex = []
    for rest in itertools.combinations(range(first + 1, 33), 6):
        T = (first,) + rest
        if any(f(T) for _, f in TESTS): continue
        r = ladder_nudge(T)
        if r is None or r[0] != 2: continue
        t = r[2]; delta = t - F(1, 2)
        ev = [d for d in T if d % 2 == 0]; od = [d for d in T if d % 2]
        ev_iso = all(nd(e * delta) >= F(1, 8) for e in ev)
        emin, emax = min(ev), max(ev)
        at_bound = abs(delta) == F(1, 8 * emin)
        r1_ev = emax <= 7 * emin
        c[('evens isolated at delta' if ev_iso else 'evens NOT isolated at delta',
           'delta = +-1/(8 e_min)' if at_bound else 'delta other',
           'evens satisfy R1' if r1_ev else 'evens not R1', f'{len(ev)} evens')] += 1
        if len(ex) < 6 and not at_bound: ex.append((T, delta, ev, od))
    return c, ex

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 27))
    c = Counter(); ex = []
    for a, b in parts: c.update(a); ex += b
    print(f"half-lap settled sets: {sum(c.values())}")
    for k, v in sorted(c.items(), key=lambda x: -x[1])[:14]: print(f"  {k}: {v}")
    for T, d, ev, od in ex: print(f"  e.g. T {T}: t = 1/2 + ({d}); evens {ev} at {[round(float((e * d) % 1) * 8, 2) for e in ev]} eighths; odds {od} at {[round(float((F(o, 2) + o * d) % 1) * 8, 2) for o in od]}")
