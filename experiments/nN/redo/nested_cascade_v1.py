"""The block rule as the cascade read level by level (owner: the cascade derives it).  For a separated
runner: core C (slow readings), block B (fast).  Start at tau_C (the core's own event).  Alternate:
  block step: the block's cascade map from s -> the first instant >= s where every block reading is clear;
  core step : if the core is not clear there, the core's cascade map from that instant -> the next
              instant where every core reading is clear;
until both are clear.  This lands on the runner's own event t* by construction (both are the first
instant >= tau_C at which everything is clear); checked exactly.  Recorded: the number of handoffs,
for all separated runners with blocks of 3-6 and for the 252 the level-by-level construction missed.
Exact; arrangements, every runner."""
import random
from collections import Counter
from fractions import Fraction as F
from math import floor
from arrangement_lib import readings, nd
from isolated_persistence_v1 import cascade_cap
from block_rule_derived_v2 import construct
import separation_arrangements_v1 as SA
def cascade_from(ds, s, cap=200000):
    t = s; n = 0
    while n < cap:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way); n += 1
    return None
def nested(core, block, tC):
    s = tC; hand = 0
    while True:
        s = cascade_from(block, s)
        if all(nd(c * s) >= F(1, 8) for c in core): return s, hand
        s = cascade_from(core, s); hand += 1
rnd = random.Random(55); SA.rnd = rnd
H_all = Counter(); H_252 = Counter(); agree = n = 0
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
            n += 1
            tC, _ = cascade_cap(core); t, _ = cascade_cap(ds)
            s, hand = nested(core, block, tC); agree += (s == t)
            H_all[hand] += 1
            if construct(core, block, tC) is None: H_252[hand] += 1
print(f"{n} separated runners: the level-by-level cascade lands on the runner's event {agree}/{n}")
print(f"   core-block handoffs, all: {sorted(H_all.items())}")
print(f"   core-block handoffs, the {sum(H_252.values())} the construction missed: {sorted(H_252.items())}")
