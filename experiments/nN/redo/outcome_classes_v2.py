# OUTCOME classes: group arrangements by where the cascade ends -- the isolation interval it lands in.
# Outcome = (opener (rank, lap): the zone whose exit is the landing; closer (rank, lap): the first zone entry after the landing;
#            lap vector l_y = round(rho_y * R*/8): the lap each runner is on at the landing, constant over the clear window).
# Exact Fractions.  rank 1 = d_min (reading 1).
import sys
from fractions import Fraction as F
from math import floor
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
def outcome(rhos):
    rhos = sorted(rhos); m = rhos[0]; rhos = [r / m for r in rhos]
    steps, R = path(rhos)
    opener = (steps[-1]['setter'] + 1, steps[-1]['lap']) if steps else None
    # closer: smallest entry (8j-1)/rho_y >= R over y, j >= 1
    best = None
    for y, r in enumerate(rhos):
        j = max(1, -(-(R * r + 1) // 8))            # smallest j with 8j-1 >= R*r
        j = int(j)
        while 8 * j - 1 < R * r: j += 1
        while j > 1 and 8 * (j - 1) - 1 >= R * r: j -= 1
        e = F(8 * j - 1) / r
        if best is None or e < best[0] or (e == best[0] and (y + 1) < best[1][0]): best = (e, (y + 1, j))
    lap = tuple(int(floor(R * r / 8 + F(1, 2))) for r in rhos)
    return dict(R=R, opener=opener, closer=best[1], width=best[0] - R, lap=lap, nmoves=len(steps), path=tuple((s['setter'] + 1, s['lap']) for s in steps))
if __name__ == "__main__":
    for rh in ([1,2,3,4,5,6,7], [1,F(71,10),F(72,10),F(73,10),F(74,10),F(75,10),F(76,10)]):
        o = outcome([F(x) for x in rh]); print([float(x) for x in rh], {k: (float(v) if isinstance(v, F) else v) for k, v in o.items()})
