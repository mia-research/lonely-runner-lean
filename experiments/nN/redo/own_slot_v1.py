"""Owner (2026-09-25): at a runner's isolation point every other runner is within 1/8 either side of ITS
OWN isolation point -- the vertex it holds at the global event: for runner k and class a (odd), runner j
(by speed rank) sits at ((rank_j - rank_k) * a mod 8)/8.  At runner k's cascade event t*, position
p_j = (v_j - v_k) t* mod 1.  Test: some class a with every j != k within 1/8 (circular) of its vertex.
Arrangements: uniform [1,10^6], clustered, slow-plus-fast (separation_arrangements_v1 families), and the
AP (1..8) with speeds deformed by up to 1/20 and 1/5.  Every runner; exact."""
import random
from collections import Counter
from fractions import Fraction as F
from arrangement_lib import readings
from isolated_persistence_v1 import cascade_cap
import separation_arrangements_v1 as SA
def circ(x): x = x % 1; return min(x, 1 - x)
def test(V, k, t):
    best = None
    for a in (1, 3, 5, 7):
        off = [j for j in range(8) if j != k and circ((V[j] - V[k]) * t - F(((j - k) * a) % 8, 8)) > F(1, 8)]
        if best is None or len(off) < best[1]: best = (a, len(off))
    return best
rnd = random.Random(56); SA.rnd = rnd
fams = {n: (lambda n=n: SA.family(n)) for n in ("uniform", "clustered", "slow-plus-fast")}
fams["AP deformed 1/20"] = lambda: [(i + 1) * (1 + F(rnd.randrange(-500, 501), 10000)) for i in range(8)]
fams["AP deformed 1/5"] = lambda: [(i + 1) * (1 + F(rnd.randrange(-2000, 2001), 10000)) for i in range(8)]
for name, gen in fams.items():
    c = Counter(); tot = 0
    for _ in range(250):
        V = sorted(set(gen()))
        if len(V) < 8: continue
        for k in range(8):
            t, _ = cascade_cap(readings(V, k)); tot += 1
            a, off = test(V, k, t); c[off] += 1
    print(f"{name}: {tot} runners; runners with EVERY other runner within 1/8 of its own global-event vertex (best class): {c[0]}/{tot};  "
          f"number of runners outside, by count: {dict(sorted(c.items()))}")
