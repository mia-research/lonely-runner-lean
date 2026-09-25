"""What does the cascade do for runners whose readings are separated with a block of 3-6 (no proved rule
yet)?  Arrangements from separation_arrangements_v1's families, EVERY runner; for the separated ones
with block f in 3..6, read: the core's own isolation event tau_C (cascade on the core readings alone),
the runner's isolation event t* (cascade on all its readings), t*/tau_C, which reading pins t* (sits
exactly at 1/8 or 7/8), whether it is a core or block reading, and how many block turns (min block * t)
fit between tau_C and t*.  Exact."""
import random
from collections import Counter
from arrangement_lib import readings, nd, F
from isolated_persistence_v1 import cascade_cap
exec(open('separation_arrangements_v1.py').read().split("for name in (")[0].split("rnd = random.Random(52)")[1].replace("def family", "def family") if False else "")
import separation_arrangements_v1 as SA
rows = Counter(); ratio = Counter(); pinkind = Counter(); same_cell = Counter(); ex = []
rnd = random.Random(55); SA.rnd = rnd
for name in ("uniform", "clustered", "slow-plus-fast"):
    for _ in range(300):
        V = sorted(set(SA.family(name)))
        if len(V) < 8: continue
        for k in range(8):
            ds = readings(V, k)
            rs = [(F(ds[i + 1], ds[i]), i) for i in range(len(ds) - 1)]
            r, i = max(rs)
            if r < 9: continue
            core, block = ds[:i + 1], ds[i + 1:]; f = len(block)
            if f < 3: continue
            tC, _ = cascade_cap(core); t, _ = cascade_cap(ds)
            rows[f] += 1
            q = t / tC
            ratio['t* = tau_C' if q == 1 else ('t* in (tau_C, 2 tau_C)' if q < 2 else 't* >= 2 tau_C')] += 1
            pins = [d for d in ds if (d * t) % 1 in (F(1, 8), F(7, 8))]
            pinkind['block' if all(p in block for p in pins) else ('core' if all(p in core for p in pins) else 'both')] += 1
            # is t* inside the core's first lonely cell?  (core clear on [tau_C, t*])
            steps = [tC + (t - tC) * F(j, 64) for j in range(65)]
            same_cell['core clear all the way from tau_C to t*' if all(all(nd(c * s) >= F(1, 8) for c in core) for s in steps) else 'core blocked in between'] += 1
            if len(ex) < 6 and f >= 5: ex.append((name, V, V[k], core, block, float(tC), float(t), pins))
print(f"separated runners with block 3-6 by size: {dict(sorted(rows.items()))}")
print(f"   isolation event vs the core's own event: {dict(ratio)}")
print(f"   pinned by: {dict(pinkind)};  {dict(same_cell)}")
for name, V, s, core, block, tC, t, pins in ex:
    print(f"   {name}: runner {s} of {V}: core readings {core}, block {block}; tau_C = {tC:.6f}, t* = {t:.6f}; pinned by {pins}")
