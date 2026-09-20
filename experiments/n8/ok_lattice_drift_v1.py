"""ok_lattice_drift_v1 -- do isolation times drift off the exact p/8 locations?

n = 8, individual isolation, threshold 1/8.  Base AP (1,...,8), one runner
displaced by eps.  Three measurements:

  [1] lattice occupancy -- for every runner, how many of its isolation windows
      contain a point of the eighth-lattice {m/8} and how many have moved off it.
  [2] drift -- displacement of the window nearest t = k + p/8, as k advances.
  [3] ownership -- which of the moved runner's own constraints is exactly at its
      1/8 boundary at each window, i.e. which constraint the window is pinned to.

[3] is the one that carries information.  The drift RATE is an arithmetic
identity, not a measurement: with r1 = 1+eps the constraint to r6 is d = 5-eps,
windows pinned to it recur every 5 d-periods, and 5/d - 1 = (5-d)/d = eps/d.
What is not forced is WHICH constraint owns the window nearest a given lattice
point -- and ownership changes along the time axis.

Individual, not global: each runner's constraint set is its own n-1 = 7
differences.  Global isolation would use all C(8,2) = 28 pairs and would give
all eight runners the identical good set.

BSM, original time, exact Fractions.  See ok_ap_transit_r1_r2_v1 for the engine.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ok_ap_transit_r1_r2_v1 import record
from fractions import Fraction as F

def occupancy(V):
    """[1] per runner: windows on / off the eighth-lattice."""
    out = []
    for i in range(len(V)):
        r = record(V, i)
        on = off = 0
        for (a, b) in r["windows"]:
            if (b * 8).__floor__() >= (a * 8).__ceil__(): on += 1
            else: off += 1
        out.append((r["count"], on, off, r["period"]))
    return out

def pinned_to(V, mover, t):
    """[3] which of the mover's constraints is exactly at ||d t|| = 1/8."""
    res = []
    for j in range(len(V)):
        if j == mover: continue
        d = abs(V[mover] - V[j]); x = (d * t) % 1
        if min(x, 1 - x) == F(1, 8): res.append(d)
    return res

def drift(V, mover, p, kmax=10):
    """[2] displacement of the window nearest t = k + p/8, with its owner."""
    r = record(V, mover); rows = []
    for k in range(kmax):
        tgt = F(k) + F(p, 8)
        a, b = min(r["windows"], key=lambda w: min(abs(w[0] - tgt), abs(w[1] - tgt)))
        disp = a - tgt if a > tgt else (b - tgt if b < tgt else F(0))
        rows.append((k, tgt, a, disp, pinned_to(V, mover, a)))
    return rows

if __name__ == "__main__":
    AP = [F(x) for x in range(1, 9)]
    for label, V in (("AP (control)", AP), ("r1 = 1.01", [F(101,100)] + AP[1:])):
        print(f"\n{label}: V = ({', '.join(str(v) for v in V)})")
        print(f"{'runner':>6} {'windows':>8} {'on lattice':>11} {'off lattice':>12}")
        for i, (c, on, off, P) in enumerate(occupancy(V)):
            print(f"{i+1:>6} {c:>8} {on:>11} {off:>12}")
    for eps in (F(1,100), F(1,20), F(1,10)):
        V = [F(1) + eps] + AP[1:]
        print(f"\ndrift, eps = {eps}, tracking t = k + 5/8:")
        for k, tgt, a, disp, own in drift(V, 0, 5, 6):
            print(f"  k={k}  target {str(tgt):>8}  start {str(a):>14}  "
                  f"disp {float(disp):>10.6f}  owner {[str(d) for d in own]}")
