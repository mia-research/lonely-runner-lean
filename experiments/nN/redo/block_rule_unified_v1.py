"""The block rule, unified (2a + 2b): a separated runner's event t* is at the core's first isolation
tau_C if the block is clear there; otherwise it lies in the core's FIRST lonely cell of positive length
after tau_C (the core's cascade continued past a point-cell).  Checked exactly on all 3,107 separated
runners with blocks of 3-6 (arrangements, every runner)."""
import random
from collections import Counter
from fractions import Fraction as F
from math import floor, ceil
from arrangement_lib import readings, nd
from isolated_persistence_v1 import cascade_cap
from nested_cascade_v1 import cascade_from
import separation_arrangements_v1 as SA
def cell_end(core, t):
    return min((ceil(c * t + F(1, 8)) - F(1, 8)) / c for c in core)   # a reading exactly at 7/8 enters its zone now
def first_positive_cell(core, tC):
    s = tC
    while True:
        e = cell_end(core, s)
        if e > s: return s, e
        s = cascade_from(core, s + F(1, 10**15))
if __name__ == '__main__':
    rnd = random.Random(55); SA.rnd = rnd
    tab = Counter(); bad = []
    for name in ("uniform", "clustered", "slow-plus-fast"):
        for _ in range(300):
            V = sorted(set(SA.family(name)))
            if len(V) < 8: continue
            for k in range(8):
                ds = readings(V, k)
                rs = [(F(ds[i + 1], ds[i]), i) for i in range(len(ds) - 1)]; r, i = max(rs)
                if r < 9: continue
                core, block = ds[:i + 1], ds[i + 1:]
                if len(block) < 3: continue
                tC, _ = cascade_cap(core); t, _ = cascade_cap(ds)
                s, e = first_positive_cell(core, tC)
                if t == tC: tab['event at tau_C (block clear there)'] += 1
                elif s <= t <= e: tab['event in the first positive-length core cell'] += 1
                else:
                    tab['NEITHER'] += 1
                    if len(bad) < 5: bad.append((core, block, str(tC), str(s), str(e), float(t)))
    print(f"{sum(tab.values())} separated runners (block 3-6): {dict(tab)}")
    for b in bad: print(f"   neither: core {b[0]}, block {b[1]}: tau_C {b[2]}, first positive cell [{b[3]}, {b[4]}], event {b[5]:.7f}")
