"""REDO of cascade_map_v1 (which used difference sets): along each runner's cascade, in arrangements,
every runner -- how many steps each other runner is in the way (Theorem 13(5): the event exists iff
all are finite), and whether the move is set by the subject's nearest runner on that side of the circle.
Random arrangements of 8 distinct speeds in [1,200] and in [1,10^6]; exact."""
import random
from collections import Counter
from arrangement_lib import readings, nd, F, floor
rnd = random.Random(53)
def trace(ds):
    t = F(1, 8) / min(ds); inway = Counter(); nb = [0, 0]; n = 0
    while n < 20000:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return n, inway, nb
        for d in way: inway[d] += 1
        opens = {d: (F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way}
        mover = max(way, key=lambda d: opens[d])
        pos = {d: (d * t) % 1 for d in ds}; ahead = pos[mover] < F(1, 2)
        same = [d for d in ds if (pos[d] < F(1, 2)) == ahead]
        dist = (lambda d: pos[d]) if ahead else (lambda d: 1 - pos[d])
        nb[0] += 1; nb[1] += min(same, key=dist) == mover
        t = opens[mover]; n += 1
    return None, inway, nb
for hi in (200, 10**6):
    steps = Counter(); mb = Counter(); nbt = [0, 0]; runners = 0
    for _ in range(500):
        V = sorted(rnd.sample(range(1, hi + 1), 8))
        for k in range(8):
            n, inway, nb = trace(readings(V, k)); runners += 1
            steps[n] += 1; mb[max(inway.values()) if inway else 0] += 1
            nbt[0] += nb[0]; nbt[1] += nb[1]
    print(f"arrangements in [1,{hi}], {runners} runners: cascade steps {sorted(steps.items(), key=lambda x: (x[0] is None, x[0]))}")
    print(f"   most steps any one runner is in the way: {sorted(mb.items())};  move set by the nearest runner on that side: {nbt[1]}/{nbt[0]}")
