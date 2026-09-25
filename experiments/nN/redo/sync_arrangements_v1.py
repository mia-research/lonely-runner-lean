"""REDO of R / the synchronised block, in the framework's frame (supersedes sync_block_v1/v2,
sync_R_grid_v1, sync_divisible_cascade_v1, sync_first_event_v1, which evaluated one runner's
difference set with that runner at speed 0).

Arrangements of 8 distinct positive speeds: a slow group of s runners (speeds in [1, 60]) and a fast
synchronised group of 8 - s runners at N + e_i (0 <= e_i <= 60, N = 10^5).  Includes slow groups whose
speeds are multiples of 7 and of 42, the condition the voided work singled out.  For EVERY runner: the
exact cascade (moves, instant, scale D = 1/(8t)), the tier (AP at g / grid at d_min / enlarged), and
whether the arrangement is a grid mod 8.
"""
import random
from collections import Counter
from arrangement_lib import *
rnd = random.Random(49); N = 10**5
res = Counter(); by_family = {}
for fam in ("random slow", "slow multiples of 7", "slow multiples of 42"):
    tiers = Counter(); moves = Counter(); lonely = 0; runners = 0; grids = 0
    for _ in range(300):
        s = rnd.choice((1, 2, 3))
        if fam == "random slow": slow = rnd.sample(range(1, 61), s)
        elif fam == "slow multiples of 7": slow = [7 * x for x in rnd.sample(range(1, 9), s)]
        else: slow = [42 * x for x in rnd.sample(range(1, 4), s)]
        fast = [N + e for e in rnd.sample(range(0, 61), 8 - s)]
        V = sorted(set(slow + fast))
        if len(V) < 8: continue
        grids += is_grid(V)
        for k in range(8):
            t, m = cascade(readings(V, k)); runners += 1; lonely += 1
            moves[m] += 1; tiers[tier(V, k)] += 1
    print(f"{fam}: {runners} runners in {runners // 8} arrangements (grids mod 8: {grids});  every runner's cascade reaches its isolation event: {lonely}/{runners}")
    print(f"   cascade moves per runner: {sorted(moves.items())};  tier: {dict(tiers)}")
