"""Statement 2: the fast block has a jointly clear instant inside the core's first lonely cell of positive
length.  For every separated runner (block 3-6; arrangements, every runner; exact) whose block is NOT
clear at the core's first isolation tau_C (1,770 in block_rule_unified_v1):
  available = (cell length) * min(block)       -- block turns inside the cell
  needed    = (first block-clear instant from the cell start - cell start) * min(block)
Reported: distributions, the least margin available - needed, and both split by whether the block has
a nearly synchronised sub-cluster (two block readings within relative 1/9)."""
import random
from collections import Counter
from fractions import Fraction as F
from arrangement_lib import readings, nd
from isolated_persistence_v1 import cascade_cap
from nested_cascade_v1 import cascade_from
from block_rule_unified_v1 import first_positive_cell
import separation_arrangements_v1 as SA
def has_sync(block): return any(9 * (block[i + 1] - block[i]) <= block[i] for i in range(len(block) - 1))
rnd = random.Random(55); SA.rnd = rnd
rows = {True: [], False: []}
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
            tC, _ = cascade_cap(core)
            if all(nd(b * tC) >= F(1, 8) for b in block): continue
            s, e = first_positive_cell(core, tC)
            tb = cascade_from(block, s)
            mb = min(block)
            rows[has_sync(block)].append((float((e - s) * mb), float((tb - s) * mb), core, block))
def q(xs, p): xs = sorted(xs); return xs[int(p * (len(xs) - 1))]
for sync, rr in rows.items():
    av = [a for a, n, *_ in rr]; ne = [n for a, n, *_ in rr]; mg = [a - n for a, n, *_ in rr]
    worst = min(rr, key=lambda x: x[0] - x[1])
    print(f"block {'WITH' if sync else 'without'} a nearly synchronised sub-cluster: {len(rr)} runners")
    print(f"   turns available: min {min(av):.2f}, median {q(av,.5):.1f};  turns needed: median {q(ne,.5):.3f}, 99% {q(ne,.99):.3f}, max {max(ne):.3f};  least margin {min(mg):.3f}")
    print(f"   tightest: core {worst[2]}, block {worst[3]}: available {worst[0]:.3f}, needed {worst[1]:.3f}")
