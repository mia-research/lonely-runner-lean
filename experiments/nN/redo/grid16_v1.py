"""Owner: in the grid 1..7, 16 (all eight runners moving), the fast runner 16 fills the place of 8 but probably also
coincides with other positions, delaying global isolation.  For each runner: its cascade isolation, the lonely set over
one period (exact), and at each of its lonely components' blocked neighbours whether runner 16 is the one in the way.
Also the same arrangement with 8 in place of 16 (the progression 1..8) for comparison."""
from fractions import Fraction as F
from arrangement_lib import readings, cascade, nd
from grid_map_v1 import lonely_set

def study(V):
    print(f"\nspeeds {V}")
    for k, v in enumerate(V):
        ds = readings(V, k); t, mv = cascade(ds)
        C = lonely_set(ds, F(1))
        # the first instants after the bound where the subject is blocked ONLY by the fast runner
        fast = V[-1]
        only_fast = 0; blocked_by_fast = 0
        grid = [F(i, 800) for i in range(1, 800)]
        for s in grid:
            way = [u for u in V if u != v and nd((u - v) * s) < F(1, 8)]
            if way:
                blocked_by_fast += fast in way and v != fast
                only_fast += way == [fast]
        print(f"  runner speed {v}: isolation t = {t} (R = {8 * min(ds) * t}), {mv} cascade moves; lonely components in one lap: {len(C)}; "
              f"blocked only by {fast} at {only_fast} of 799 sample instants")
study([1, 2, 3, 4, 5, 6, 7, 16])
study([1, 2, 3, 4, 5, 6, 7, 8])
