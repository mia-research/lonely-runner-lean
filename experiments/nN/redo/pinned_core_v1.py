"""Statement 2b: a core pinned on both sides at its first isolation tau_C = 1/(8a) (a = the core's least
reading at 1/8, b = (8m+7)a at 7/8).  Prediction: the core's next lonely cell starts at b's next opening
t1 = (8m+9)/(8b), where b reads exactly 1/8 and a reads (8m+9)/(8(8m+7)) > 1/8; the block then has
>= ~6.75 turns in it (min block >= 9 max core >= 9b).  Checked exactly on every doubly pinned separated
runner (block 3-6): (i) is the core's next lonely instant after tau_C exactly t1?  (ii) the cell
[t1, end); (iii) does the runner's event t* lie in it?  (iv) block turns in the cell."""
import random
from collections import Counter
from fractions import Fraction as F
from math import floor, ceil
from arrangement_lib import readings, nd
from isolated_persistence_v1 import cascade_cap
from nested_cascade_v1 import nested, cascade_from
import separation_arrangements_v1 as SA
def cell_end(core, t):
    return min((ceil(c * t + F(1, 8)) - F(1, 8)) / c for c in core)   # a reading exactly at 7/8 enters its zone now
rnd = random.Random(55); SA.rnd = rnd
tab = Counter(); turns = []; ex = []
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
            ahead = [c for c in core if (c * tC) % 1 == F(1, 8)]; behind = [c for c in core if (c * tC) % 1 == F(7, 8)]
            if not (ahead and behind): continue
            a, b = min(ahead), min(behind)
            m = floor(b * tC)                        # b reads m + 7/8 at tau_C
            t1 = F(8 * m + 9, 8 * b)
            nxt = cascade_from(core, tC + F(1, 10**12))   # the core's next lonely instant after tau_C
            tab['next core instant == t1' if nxt == t1 else 'next core instant != t1'] += 1
            end = cell_end(core, t1); bt = (end - t1) * min(block); turns.append(float(bt))
            s, hand = nested(core, block, tC); t, _ = cascade_cap(ds)
            where = 'at tau_C' if t == tC else ('in [t1, end]' if t1 <= t <= end else 'later')
            tab[(f'handoffs {hand}', f'event {where}')] += 1
            if nxt != t1 or where == 'later':
                if len(ex) < 6: ex.append((core, block, str(tC), str(t1), str(nxt), float(t), hand))
print(f"doubly pinned separated runners: {sum(v for k2, v in tab.items() if isinstance(k2, str))}")
for key in sorted(tab, key=str): print(f"  {key}: {tab[key]}")
print(f"  block turns in the cell starting at t1: min {min(turns):.2f}, median {sorted(turns)[len(turns)//2]:.1f}")
for e in ex: print(f"   exception: core {e[0]}, block {e[1]}: tau_C {e[2]}, t1 {e[3]}, core's next instant {e[4]}, event {e[5]:.6f}, handoffs {e[6]}")
