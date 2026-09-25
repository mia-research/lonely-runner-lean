"""Step 2: cases where the core's cell closes before the fast train opens a gap (a handoff at the core's
scale).  Arrangements (every speed positive): subject s = 1000, core runners at s + c (c in C, 1-2 slow
readings), a fast train at s + N + e (e in E: 4-5 whole-number offsets), N = 10^5.  For the subject: the
core's first lonely cell of positive length [a, b]; the full event t* (exact cascade).  Handoff = t* > b.
For each handoff: which core cell t* lies in (index), the train's largest offset gap at that cell's start,
the gcd g of the offsets and whether the core is blocked at every period point k/g.  Exact."""
import random
from collections import Counter
from fractions import Fraction as F
from math import gcd, ceil
from functools import reduce
from arrangement_lib import readings, nd
from isolated_persistence_v1 import cascade_cap
from nested_cascade_v1 import cascade_from
from block_rule_unified_v1 import first_positive_cell
from block_rule_derived_v1 import max_gap
rnd = random.Random(58); N = 10**5; s0 = 1000
tab = Counter(); ex = []
for trial in range(4000):
    C = sorted(rnd.sample(range(1, 60), rnd.choice((1, 2))))
    E = [0] + sorted(rnd.sample(range(1, 80), rnd.choice((3, 4))))
    V = [s0] + [s0 + c for c in C] + [s0 + N + e for e in E]
    if len(set(V)) != len(V) or len(V) > 8: continue
    ds = readings(V, 0)
    tC, _ = cascade_cap(C)
    a, b = first_positive_cell(C, tC)
    t, n = cascade_cap(ds)
    if t <= b: tab['no handoff'] += 1; continue
    tab['HANDOFF'] += 1
    # which core cell holds t*?
    s, idx = a, 0
    while True:
        s, e = first_positive_cell(C, s); idx += 1
        if s <= t <= e: break
        s = cascade_from(C, e + F(1, 10**15))
    g = reduce(gcd, [x for x in E if x]) if any(E) else 1
    blocked_at_periods = all(any(nd(c * F(k, g)) < F(1, 8) for c in C) for k in range(1, 8 * g + 1))
    tab[('core cell index', idx)] += 1
    tab[('core blocked at every period point k/g', blocked_at_periods)] += 1
    if len(ex) < 8:
        ex.append((C, E, float(a), float(b), float(t), idx, float(max_gap([x * a for x in E])), float(max_gap([x * s for x in E])), g, blocked_at_periods))
for k in sorted(tab, key=str): print(f"  {k}: {tab[k]}")
for C, E, a, b, t, idx, g0, g1, g, bl in ex:
    print(f"   core {C}, train offsets {E}: first core cell [{a:.5f}, {b:.5f}], event {t:.5f} in core cell #{idx}; "
          f"train gap at first cell {g0:.3f}, at event's cell start {g1:.3f}; gcd {g}, core blocked at all k/g: {bl}")
