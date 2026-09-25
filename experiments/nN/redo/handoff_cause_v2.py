"""handoff_cause_v1 refuted the offsets explanation (44 of 45 handoff runners have their offsets gapped at
tau_C).  Next hypothesis, from the examples: a handoff happens exactly when the CORE's own first
isolation is pinned on both sides -- some core reading exactly at 1/8 and another exactly at 7/8 at
tau_C -- so the core's first lonely cell is a single point and the block has no room.  Tested on all
3,107 separated runners (block 3-6): pinned-both-sides vs handoffs.  Exact."""
import random
from collections import Counter
from fractions import Fraction as F
from arrangement_lib import readings
from isolated_persistence_v1 import cascade_cap
from nested_cascade_v1 import nested
import separation_arrangements_v1 as SA
rnd = random.Random(55); SA.rnd = rnd
tab = Counter(); pins = Counter()
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
            ahead = [c for c in core if (c * tC) % 1 == F(1, 8)]; behind = [c for c in core if (c * tC) % 1 == F(7, 8)]
            both = bool(ahead) and bool(behind)
            tab[("handoff" if hand else "no handoff", "core pinned both sides at tau_C" if both else "core not pinned both sides")] += 1
            if hand: pins[(tuple(ahead), tuple(behind))] += 1
for key in sorted(tab): print(f"  {key}: {tab[key]}")
print(f"  handoff runners' core pinners (ahead at 1/8, behind at 7/8): {dict(pins.most_common(8))}")
