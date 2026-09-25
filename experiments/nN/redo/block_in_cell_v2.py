"""The block-in-cell cases that need more than 2 block turns (block_in_cell_v1): cluster structure of the
block (synchronised clusters, relative spread <= 1/9), each cluster's offsets and spread E, the core, and
the time scales: the needed time, the cell length, 1/E of the largest cluster, 1/max(core).  Exact."""
import random
from fractions import Fraction as F
from arrangement_lib import readings, nd
from isolated_persistence_v1 import cascade_cap
from nested_cascade_v1 import cascade_from
from block_rule_unified_v1 import first_positive_cell
from block_rule_derived_v1 import clusters
import separation_arrangements_v1 as SA
rnd = random.Random(55); SA.rnd = rnd; shown = 0; n_big = 0; ratio = []
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
            s, e = first_positive_cell(core, tC); tb = cascade_from(block, s); mb = min(block)
            if (tb - s) * mb <= 2: continue
            n_big += 1
            cl = clusters(block); big = max(cl, key=lambda c: c[-1] - c[0] if len(c) > 1 else 0)
            E = big[-1] - big[0]
            ratio.append(float((tb - s) * E))
            if shown < 8:
                shown += 1
                print(f"core {core}, clusters {cl}: needed {float(tb - s):.5f} (= {float((tb-s)*mb):.1f} block turns), cell {float(e - s):.5f}; "
                      f"widest cluster spread E = {E}: needed x E = {float((tb - s) * E):.3f}, cell x max(core) = {float((e - s) * max(core)):.3f}")
print(f"{n_big} runners need > 2 block turns; needed time x (widest cluster spread E): min {min(ratio):.3f}, max {max(ratio):.3f}")
