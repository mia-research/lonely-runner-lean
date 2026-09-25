"""Statement 2 of the block rule: what distinguishes the runners whose block needs 1-2 handoffs to land
in a core-clear cell (nested_cascade_v1: 45 of 3,107)?  For each separated runner (block 3-6): the
largest synchronised cluster (relative spread <= 1/9); whether that cluster's offsets leave a gap > 1/4
at the core's event tau_C; the number of handoffs.  Exact; arrangements, every runner."""
import random
from collections import Counter
from fractions import Fraction as F
from arrangement_lib import readings
from isolated_persistence_v1 import cascade_cap
from block_rule_derived_v1 import clusters, max_gap
from nested_cascade_v1 import nested
import separation_arrangements_v1 as SA
rnd = random.Random(55); SA.rnd = rnd
tab = Counter(); ex = []
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
            tC, _ = cascade_cap(core); s, hand = nested(core, block, tC)
            cl = clusters(block); big = max(cl, key=len)
            gapped = max_gap([(x - big[0]) * tC for x in big]) > F(1, 4) if len(big) > 1 else True
            key = ("handoff" if hand else "no handoff", f"largest cluster {len(big)}", "offsets gapped at tau_C" if gapped else "offsets NOT gapped at tau_C")
            tab[key] += 1
            if hand and len(ex) < 6: ex.append((core, cl, float(tC), float(s), hand))
for key in sorted(tab): print(f"  {key}: {tab[key]}")
for core, cl, tC, s, hand in ex: print(f"   handoff example: core {core}, clusters {cl}: tau_C {tC:.6f}, event {s:.6f}, handoffs {hand}")
