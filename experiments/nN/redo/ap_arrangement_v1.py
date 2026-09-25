"""REDO item 2 (supersedes ap_local_v1, which deformed the end runner's disparities with that runner at
speed 0; ap_neighbours_v1 was already in the arrangement frame and stands).

The AP arrangement (1, 2, ..., 8), speeds deformed v_i -> i (1 + r_i), |r_i| <= rho.  EVERY runner's
isolation event read with the exact cascade map; reported: reached / not, the event's position relative
to the AP's class instants a/8 (a odd), and whether it sits at an opening of one of the runner's two
circle neighbours at the global event (runners k +- a mod 8).
"""
import random
from collections import Counter
from arrangement_lib import readings, nd, F, floor
from isolated_persistence_v1 import cascade_cap
rnd = random.Random(51)
for rho in (F(1, 10), F(1, 20), F(1, 50), F(1, 100), F(1, 200)):
    ok = tot = 0; cls = Counter(); by_neighbour = 0; ends = Counter()
    for _ in range(250):
        W = [(i + 1) * (1 + F(rnd.randrange(-10**4, 10**4 + 1), 10**4) * rho) for i in range(8)]
        for k in range(8):
            t, n = cascade_cap(readings(W, k)); tot += 1
            if t is None: continue
            ok += 1
            a = next((a for a in (1, 3, 5, 7) if abs(t - F(a, 8)) < F(1, 32)), None)
            cls[a if a else 'other'] += 1
            if a:
                nbrs = [((k + a) % 8), ((k - a) % 8)]
                pinned = [j for j in nbrs if nd((W[j] - W[k]) * t) == F(1, 8)]
                by_neighbour += bool(pinned)
            if k in (0, 7): ends[a if a else 'other'] += 1
    print(f"|r| <= {rho}: runners reaching their event {ok}/{tot};  event near class a/8: {dict(sorted(cls.items(), key=str))};  "
          f"of those, pinned by a circle neighbour of the global event: {by_neighbour};  end runners' classes {dict(sorted(ends.items(), key=str))}")
