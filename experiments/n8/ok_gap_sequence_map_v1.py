"""ok_gap_sequence_map_v1 -- the gap sequence over a transit.

n = 8, individual isolation, threshold 1/8.  Base AP (1,...,8), one runner
transited.  BSM supplies the loneliness INTERVALS, so we know where on the track
each runner achieves its loneliness, not merely that it does.

At any instant the eight runners sit in a cyclic order and define eight gaps
summing to 1.  A runner is lonely iff BOTH of its adjacent gaps are >= 1/8
(verified: 47,904 runner-instants, 0 disagreements).  So the object that governs
everything is the gap sequence, and this maps it.

For every runner at every transit position, at the START of its first loneliness
window, record:

  moment      t*            when it becomes lonely
  position    v_i*t* mod 1  where on the track it is then
  behind/ahead              which runners flank it at that instant
  gap behind / gap ahead    its two adjacent gaps
  binding                   which of the two is exactly 1/8 -- the constraint
                            that had been blocking it and has just opened

Speeding a runner up steals from the gap ahead and gives to the gap behind;
slowing it down does the reverse.  The maps below show what that does to
everyone else.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from ok_full_transit_sweep_v1 import runner_row

N = 8

def gap_sequence(V, t):
    """Cyclic order and the eight gaps at time t."""
    pts = sorted(((v * t) % 1, i) for i, v in enumerate(V))
    order = [i for _, i in pts]
    pos = [p for p, _ in pts]
    gaps = [(pos[(k + 1) % N] - pos[k]) % 1 for k in range(N)]
    return order, pos, gaps

def snapshot(V, i):
    """Runner i's first loneliness, described through the gap sequence."""
    r = runner_row(V, i)
    if not r["windows"]:
        return None
    t = r["windows"][0][0]
    order, pos, gaps = gap_sequence(V, t)
    k = order.index(i)
    behind, ahead = order[(k - 1) % N], order[(k + 1) % N]
    gb, ga = gaps[(k - 1) % N], gaps[k]
    binding = []
    if gb == F(1, N): binding.append(f"r{behind+1} behind")
    if ga == F(1, N): binding.append(f"r{ahead+1} ahead")
    return {"moment": t, "position": (V[i] * t) % 1, "behind": behind + 1,
            "ahead": ahead + 1, "gap_behind": gb, "gap_ahead": ga,
            "binding": ", ".join(binding) or "-", "gaps": gaps,
            "window": r["windows"][0][1] - t}

if __name__ == "__main__":
    AP = [F(x) for x in range(1, 9)]
    for r1 in (F(1,2), F(9,10), F(1), F(11,10), F(3,2), F(19,10)):
        V = list(AP); V[0] = r1
        tag = "  <- AP" if r1 == 1 else ""
        print(f"\n{'='*104}\nr1 = {r1}{tag}")
        print(f"{'runner':>7} {'moment':>9} {'position':>9} {'behind':>7} {'gap behind':>11} "
              f"{'ahead':>6} {'gap ahead':>10} {'binding':>18}")
        for i in range(8):
            s = snapshot(V, i)
            print(f"{'r'+str(i+1):>7} {float(s['moment']):>9.4f} {float(s['position']):>9.4f} "
                  f"{'r'+str(s['behind']):>7} {float(s['gap_behind']):>11.5f} "
                  f"{'r'+str(s['ahead']):>6} {float(s['gap_ahead']):>10.5f} {s['binding']:>18}")
