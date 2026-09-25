"""Mapping the cascade's own deformation (owner, 2026-09-25: the cascade's sequence of scales is the
path the isolation takes).  Exact fractions.

Cascade (PAPER_v9_1 section 7): start at the bound t0 = 1/(8 d_min); a runner is in the way when
||d t|| < 1/8; the move sends t to the LARGEST next opening (N + 1/8)/d >= t over the runners in the
way; fixed when none is.  Recorded per set: number of steps; for each runner, how many steps it is in
the way (Theorem 13(5): the event exists iff every such count is finite); and whether the runner
that sets each move is the subject's nearest runner on that side of the circle at that instant.
"""
import json, random
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
from collections import Counter
def nd(x): x = x % 1; return min(x, 1 - x)
def cascade(S, cap=10000):
    t = F(1, 8 * min(S)); steps = 0; inway = Counter(); nbr = [0, 0]
    while steps < cap:
        way = [d for d in S if nd(d * t) < F(1, 8)]
        if not way: return steps, inway, nbr, t
        for d in way: inway[d] += 1
        nxt = {d: F(floor(d * t - F(1, 8)) + 1, 1) for d in way}
        opens = {d: (nxt[d] + F(1, 8)) / d for d in way}
        mover = max(way, key=lambda d: opens[d])
        # is the mover the nearest runner on its side of the subject at t?
        pos = {d: (d * t) % 1 for d in S}
        side_ahead = pos[mover] < F(1, 2)
        same = [d for d in S if (pos[d] < F(1, 2)) == side_ahead]
        dist = lambda d: pos[d] if side_ahead else 1 - pos[d]
        nbr[0] += 1; nbr[1] += (min(same, key=dist) == mover)
        t = opens[mover]; steps += 1
    return None
H = [tuple(S) for S in json.load(open('hard_sets_41_60.json'))]
rnd = random.Random(41); R = []
while len(R) < 1500:
    S = tuple(sorted(rnd.sample(range(1, 200), 7)))
    if reduce(gcd, S) == 1: R.append(S)
for label, sets in (("1,436 rule-miss sets", H), ("1,500 random primitive 7-sets of [1,200]", R)):
    stp = Counter(); maxblock = Counter(); nb = [0, 0]; worst = None
    for S in sets:
        out = cascade(S)
        steps, inway, nbr, t = out
        stp[steps] += 1; mb = max(inway.values()) if inway else 0; maxblock[mb] += 1
        nb[0] += nbr[0]; nb[1] += nbr[1]
        if worst is None or mb > worst[0]: worst = (mb, S, steps)
    print(f"{label}: steps {sorted(stp.items())}")
    print(f"   most steps any one runner is in the way: {sorted(maxblock.items())};  worst {worst}")
    print(f"   the runner setting the move is the subject's nearest on its side: {nb[1]}/{nb[0]}")
