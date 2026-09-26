"""The nudge at the nearest runner's scale.  Every set of 7 distinct whole-number readings in 1..24 whose bound
t0 = 1/(8 m), m = d_min, is not lonely.  At t0 each reading sits at rho = d/(8m) mod 1; the colliders are within 1/8 of
0.  The cascade's first move goes to the latest collider b's exit t1 = (8k+1)/(8b): the scale is multiplied by
lambda = t1/t0 and every reading moves forward by Delta = d (t1 - t0) laps, in proportion to its size.
Per set: does t1 isolate; if not, the readings in the slot at t1, each classed
  'edge'   : clear at t0, moved forward by Delta < 3/4 across the edge 7/8
  'wrap'   : clear at t0, moved by Delta >= 3/4 (most of a lap or more)
  'back'   : a collider at t0 (not the setter) in the slot again
and the room condition for the edge class: rho + Delta <= 7/8.  Exact."""
import itertools
from fractions import Fraction as F
from math import floor
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import nd

E8 = F(1, 8)

def chunk(first):
    c = Counter(); causes = Counter(); lam = Counter()
    for rest in itertools.combinations(range(first + 1, 25), 6):
        T = (first,) + rest; m = T[0]; t0 = F(1, 8 * m)
        col = [d for d in T if nd(d * t0) < E8]
        if not col: continue
        c['bound not lonely'] += 1
        ex = {d: (F(floor(d * t0 - E8) + 1) + E8) / d for d in col}
        b = max(ex, key=lambda x: ex[x]); t1 = ex[b]
        lam[min(int(8 * (t1 / t0 - 1)), 8)] += 1          # (lambda - 1) in eighths
        slot = [d for d in T if nd(d * t1) < E8]
        if not slot: c['first move isolates'] += 1; continue
        kinds = set()
        for d in slot:
            D = d * (t1 - t0)
            if d in col: kinds.add('back')
            elif D < F(3, 4): kinds.add('edge')
            else: kinds.add('wrap')
        causes[tuple(sorted(kinds))] += 1
    return c, causes, lam

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 19))
    c = Counter(); causes = Counter(); lam = Counter()
    for a, b, l in parts: c.update(a); causes.update(b); lam.update(l)
    print(f"bound not lonely: {c['bound not lonely']}; the first move isolates: {c['first move isolates']}")
    print(f"  (lambda - 1) in eighths, floor: {sorted(lam.items())}")
    print(f"  why the first move does not isolate (kinds of readings in the slot at t1): {sorted(causes.items(), key=lambda x: -x[1])}")
