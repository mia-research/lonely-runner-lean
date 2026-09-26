"""WP2 continued: perturbation paths through Case C arrangements (the subject = slowest runner, g_1 < W/22).  One runner
moved step by step; per step: u* (event in laps of the nearest runner), WAIT (laps of d_2 after the nearest runner's
first band opens), WAIT/ROOM, the pinning runner(s), and jumps.  Exact."""
from fractions import Fraction as F
from case_c_map_v1 import measure
bases = {'even rest':            [1000, 1020, 1520, 2010, 2490, 3000, 3515, 4000],
         'clumped + outliers':   [1000, 1003, 1010, 1017, 1030, 5030, 5040, 9040],
         'even rest + a clump':  [1000, 1007, 1507, 1512, 1516, 2016, 2510, 3000]}
for name, B in bases.items():
    print(f"\n=== {name}: {B}  (g1 = {B[1]-B[0]}, W = {B[-1]-B[0]})")
    for j in (3, 5, 7):
        prev = None; rows = []
        for dl in range(-40, 41, 8):
            V = list(B); V[j] += dl
            if len(set(V)) < 8 or sorted(V) != V or V[1] - V[0] > (V[-1] - V[0]) / 22: continue
            u, wait, room, pins = measure(V)
            jump = prev is not None and u != prev; prev = u
            rows.append(f"      delta={dl:>4d} u*={float(u):.4f} wait={float(wait):.3f} laps  wait/room={float(wait/room):.4f} pins={pins}{' jump' if jump else ''}")
        print(f"   runner {j+1} moved:"); print("\n".join(rows))
