"""Owner's claim (2026-09-25): placing every runner in its AP segment at the cascade's scale, only the
subject's two neighbours can be in its isolation zone; the other five are confined to their segments.

Test along the cascade itself (as cascade_map_v1, exact).  At each step t = 1/(8D) the reading of d
is s = 8 d t = d/D in AP units; the zone is s within 1 of a multiple of 8.  A step VIOLATES
confinement if two or more runners are in the zone on the same side (s mod 8 in (0,1), or in (7,8)),
so one of them is not the subject's neighbour on that side.  Counts steps, and prints examples with
every reading, so the step can be checked by hand.
"""
import json, random
from fractions import Fraction as F
from math import floor, gcd
from functools import reduce
def nd(x): x = x % 1; return min(x, 1 - x)
def steps_of(S, cap=1000):
    t = F(1, 8 * min(S)); out = []
    while len(out) < cap:
        way = [d for d in S if nd(d * t) < F(1, 8)]
        out.append((t, way))
        if not way: return out
        opens = {d: (F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way}
        t = max(opens.values())
    return out
H = [tuple(S) for S in json.load(open('hard_sets_41_60.json'))]
rnd = random.Random(41); R = []
while len(R) < 1500:
    S = tuple(sorted(rnd.sample(range(1, 200), 7)))
    if reduce(gcd, S) == 1: R.append(S)
for label, sets in (("1,436 rule-miss sets", H), ("1,500 random 7-sets of [1,200]", R)):
    total = viol = 0; ex = []
    for S in sets:
        for t, way in steps_of(S):
            if not way: continue
            total += 1
            s = {d: 8 * d * t for d in S}
            ahead = [d for d in way if (s[d] % 8) < 1]
            behind = [d for d in way if (s[d] % 8) > 7]
            if len(ahead) >= 2 or len(behind) >= 2:
                viol += 1
                if len(ex) < 2: ex.append((S, t, {d: str(s[d]) for d in S}, ahead, behind))
    print(f"{label}: cascade steps with a runner in the way {total};  steps with 2+ runners in the zone on one side {viol}")
    for S, t, sd, ah, be in ex:
        print(f"   {S} at t = {t} (D = 1/(8t) = {1 / (8 * t)}): readings s = d/D: {sd}")
        print(f"      in the zone ahead (s mod 8 in (0,1)): {ah};  behind (s mod 8 in (7,8)): {be}")
