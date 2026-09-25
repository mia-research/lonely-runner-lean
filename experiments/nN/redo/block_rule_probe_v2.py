"""Block-turns inside the core's first lonely cell, for separated runners with block 3-6 (arrangements,
every runner; exact).  tau_C: the core's own isolation event (cascade on the core readings); its first
cell [tau_C, tau_C + l] (until a core reading next enters its zone); block turns = l * min(block).
Reported: whether the runner's event lies in that cell; the distribution of block turns; l * max(core);
and for the runners whose event lies beyond the first cell, what the cell and the block look like."""
import random
from collections import Counter
from fractions import Fraction as F
from math import floor, ceil
from arrangement_lib import readings, nd
from isolated_persistence_v1 import cascade_cap
import separation_arrangements_v1 as SA
def first_cell_end(core, tC):
    """end of the core's lonely cell that starts at tC: the least zone entry (m - 1/8)/c after tC"""
    ends = []
    for c in core:
        m = floor(c * tC + F(1, 8)) + 1          # next integer the reading approaches
        ends.append((m - F(1, 8)) / c)
    return min(ends)
rnd = random.Random(55); SA.rnd = rnd
turns_in = Counter(); lmax = Counter(); beyond = []; n_in = n = 0
def bucket(x):
    for b in (1, 2, 4, 8, 16, 64, 256):
        if x < b: return f"< {b}"
    return ">= 256"
for name in ("uniform", "clustered", "slow-plus-fast"):
    for _ in range(300):
        V = sorted(set(SA.family(name)))
        if len(V) < 8: continue
        for k in range(8):
            ds = readings(V, k)
            rs = [(F(ds[i + 1], ds[i]), i) for i in range(len(ds) - 1)]
            r, i = max(rs)
            if r < 9: continue
            core, block = ds[:i + 1], ds[i + 1:]
            if len(block) < 3: continue
            n += 1
            tC, _ = cascade_cap(core); t, _ = cascade_cap(ds)
            end = first_cell_end(core, tC); l = end - tC
            bt = l * min(block); turns_in[bucket(float(bt))] += 1; lmax[bucket(float(l * max(core) * 64)) ] += 1
            if tC <= t <= end: n_in += 1
            elif len(beyond) < 5: beyond.append((V[k], core, block, float(tC), float(end), float(t), float(bt)))
print(f"{n} separated runners (block 3-6): event inside the core's first cell {n_in}/{n}")
print(f"   block turns inside that cell (l * min block): {sorted(turns_in.items(), key=lambda x: float(x[0].split()[-1]))}")
print(f"   the cell's length in units of 1/max(core), times 64: {sorted(lmax.items(), key=lambda x: float(x[0].split()[-1]))}")
for s, core, block, tC, end, t, bt in beyond:
    print(f"   beyond: runner {s}, core {core}, block {block}: first cell [{tC:.7f}, {end:.7f}] ({bt:.2f} block turns); event t* = {t:.7f}")
