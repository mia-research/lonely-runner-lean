"""Is the resonant delay a TIME set by the fast train's differences, independent of N?  Family slow [8,12,38],
fast N + (0, d, 2d, 3d) and a tail 3d + 10.  For runner 8: the core {4, 30}'s cell opens at t_C = 3/80 (30's
opening, 30 t = 9/8); the train's offsets (fast differences) times t_C; their largest cyclic gap at t_C;
the event time t* and the delay t* - t_C, for N = 50005, 100005, 200005, 400005.  Exact."""
from fractions import Fraction as F
from arrangement_lib import readings
from isolated_persistence_v1 import cascade_cap
def max_gap(pts):
    p = sorted(set(x % 1 for x in pts)); g = [p[i + 1] - p[i] for i in range(len(p) - 1)] + [1 - p[-1] + p[0]]
    return max(g)
tC = F(3, 80)
for d in (9, 10, 11, 12):
    offs = [0, d, 2 * d, 3 * d, 3 * d + 10]
    g = max_gap([o * tC for o in offs])
    row = []
    for N in (50005, 100005, 200005, 400005):
        V = [8, 12, 38] + [N + o for o in offs]
        t, n = cascade_cap(readings(V, 0), cap=100000)
        row.append(f"N={N}: moves {n}, delay {float(t - tC):.6f}")
    print(f"d={d}: offsets {offs}, offsets x t_C = {[str(o * tC % 1) for o in offs]}, largest gap at t_C = {g} ({float(g):.4f});")
    print("      " + ";  ".join(row))
