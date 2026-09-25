"""Owner (2026-09-25): at the isolation point the runners not pinning it sit in their sections of the
circle, so their exact positions are not needed.  Measured on the 3,107 separated runners of
block_rule_probe_v1 (arrangements, every runner; exact).  Segment of a reading d at t: floor(8 (d t mod 1)),
0..7; segments 1-6 are at distance >= 1/8 from the subject by construction.
  (a) at the core's own event tau_C: the core readings that do not pin it -- which segments?
  (b) at the runner's event t*: the non-pinning readings, core and block separately -- which segments,
      and the least distance beyond 1/8 (slack)."""
import random
from collections import Counter
from fractions import Fraction as F
from math import floor
from arrangement_lib import readings, nd
from isolated_persistence_v1 import cascade_cap
import separation_arrangements_v1 as SA
rnd = random.Random(55); SA.rnd = rnd
segA = Counter(); segB_core = Counter(); segB_block = Counter(); slack_core = []; slack_block = []; n = 0
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
            for c in core:
                p = (c * tC) % 1
                if p not in (F(1, 8), F(7, 8)): segA[floor(8 * p)] += 1
            for d in ds:
                p = (d * t) % 1
                if p in (F(1, 8), F(7, 8)): continue
                s = floor(8 * p); sl = nd(d * t) - F(1, 8)
                if d in core: segB_core[s] += 1; slack_core.append(sl)
                else: segB_block[s] += 1; slack_block.append(sl)
print(f"{n} separated runners")
print(f"(a) at the core's own event, non-pinning core readings by segment: {dict(sorted(segA.items()))}")
print(f"(b) at the runner's event t*, non-pinning core readings by segment: {dict(sorted(segB_core.items()))};  least slack beyond 1/8: {float(min(slack_core)):.4f}")
print(f"    non-pinning block readings by segment: {dict(sorted(segB_block.items()))};  least slack beyond 1/8: {float(min(slack_block)):.2e}")
