"""Owner (2026-09-25): at the isolation point the other runners are NEAR their isolation point (their slot)
but not on it.  At a runner's event t* (exact cascade), scale D* = 1/(8 t*), each other reading d sits at
s = 8 d t* slot units; its slot is round(s) and its deviation delta = s - round(s), |delta| <= 1/2.
Random positions would give mean |delta| = 1/4.  Measured for non-pinning readings of: scale-free runners,
separated runners, and the 252 separated runners the level-by-level construction did not reach
(block_rule_derived_v2).  Exact; arrangements, every runner."""
import random, statistics as st
from fractions import Fraction as F
from collections import Counter
from arrangement_lib import readings
from isolated_persistence_v1 import cascade_cap
from block_rule_derived_v2 import construct
import separation_arrangements_v1 as SA
def devs(ds, t):
    out = []
    for d in ds:
        s = 8 * d * t
        if (d * t) % 1 in (F(1, 8), F(7, 8)): continue          # the pinners
        out.append(abs(s - round(s)))
    return out
rnd = random.Random(55); SA.rnd = rnd
groups = {"scale-free": [], "separated": [], "the 252": []}; zero = Counter()
for name in ("uniform", "clustered", "slow-plus-fast"):
    for _ in range(300):
        V = sorted(set(SA.family(name)))
        if len(V) < 8: continue
        for k in range(8):
            ds = readings(V, k); t, _ = cascade_cap(ds); dv = devs(ds, t)
            zero['non-pinners exactly on a slot'] += sum(1 for x in dv if x == 0); zero['non-pinners'] += len(dv)
            rs = [(F(ds[i + 1], ds[i]), i) for i in range(len(ds) - 1)]; r, i = max(rs)
            if r < 9: groups["scale-free"] += dv; continue
            groups["separated"] += dv
            core, block = ds[:i + 1], ds[i + 1:]
            if len(block) >= 3:
                tC, _ = cascade_cap(core)
                if construct(core, block, tC) is None: groups["the 252"] += dv
for g, dv in groups.items():
    q = sorted(dv)
    print(f"{g}: {len(dv)} non-pinning readings; mean |delta| = {float(st.mean(dv)):.4f} (random: 0.25);  "
          f"median {float(q[len(q)//2]):.4f};  within 1/8 of the slot {sum(1 for x in dv if x <= F(1,8))}/{len(dv)}")
print(f"{dict(zero)}")
