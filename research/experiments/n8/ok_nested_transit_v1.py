"""ok_nested_transit_v1 -- moment and distance to isolation, under nested transits.

n = 8, individual isolation, threshold 1/8.  Base AP (1,...,8).

  Stage A: r1 transits 0.1 -> 1.9 (step 0.1), r2..r8 at AP positions.
  Stage B: r1 FROZEN at each of those values, r2 then transits its own range
           (r1, 3) exclusive, step 0.1.

For every runner at every configuration, two observables:

  MOMENT    t*  = the time at which that runner FIRST becomes isolated.
  DISTANCE  L   = v_i * t*  = how far that runner has travelled by then,
                  in laps of the track.  Scale-free and per-runner.

Also recorded: the gap it achieves at t*, the length of that first isolation
window, and the cycle t* falls in (cycle = one revolution of the unmoved pack).

Ordering is kept strict -- a transit never reaches or passes a neighbour, since
at equality the two runners coincide and the configuration is really n = 7.

Engine and conventions from ok_full_transit_sweep_v1: BSM on the time axis
(boundary points and open cells separately), original time, exact Fractions with
an integer fast path, individual isolation (each runner's own seven differences).
"""
import csv, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from ok_full_transit_sweep_v1 import runner_row

STEP = F(1, 10)

def observables(V):
    """Per runner: moment, distance in laps, gap achieved, first-window length."""
    out = []
    for i in range(8):
        r = runner_row(V, i)
        if not r["windows"]:
            out.append(None); continue
        a, b = r["windows"][0]
        gap = min(min((abs(V[i]-V[j])*a) % 1, 1 - ((abs(V[i]-V[j])*a) % 1))
                  for j in range(8) if j != i)
        out.append({"moment": a, "distance": V[i] * a, "gap": gap,
                    "window": b - a, "cycle": int(a), "count": r["count"],
                    "period": r["period"]})
    return out

def frange(lo, hi):
    v, out = F(lo) + STEP, []
    while v < F(hi):
        if v > 0: out.append(v)
        v += STEP
    return out

if __name__ == "__main__":
    AP = [F(x) for x in range(1, 9)]
    rows = []
    # Stage A -------------------------------------------------------------
    for v1 in frange(0, 2):
        V = list(AP); V[0] = v1
        if len(set(V)) < 8: continue
        for i, o in enumerate(observables(V)):
            if o is None: continue
            rows.append({"stage": "A", "r1": str(v1), "r2": str(V[1]),
                         "runner": i+1, "speed": str(V[i]),
                         "moment": str(o["moment"]), "moment_f": float(o["moment"]),
                         "distance_laps": float(o["distance"]),
                         "gap": str(o["gap"]), "first_window": float(o["window"]),
                         "cycle": o["cycle"], "count": o["count"],
                         "period": str(o["period"])})
    # Stage B -------------------------------------------------------------
    for v1 in frange(0, 2):
        for v2 in frange(0, 3):
            if not (v1 < v2 < 3): continue
            V = list(AP); V[0] = v1; V[1] = v2
            if len(set(V)) < 8 or any(V[k] >= V[k+1] for k in range(7)): continue
            for i, o in enumerate(observables(V)):
                if o is None: continue
                rows.append({"stage": "B", "r1": str(v1), "r2": str(v2),
                             "runner": i+1, "speed": str(V[i]),
                             "moment": str(o["moment"]), "moment_f": float(o["moment"]),
                             "distance_laps": float(o["distance"]),
                             "gap": str(o["gap"]), "first_window": float(o["window"]),
                             "cycle": o["cycle"], "count": o["count"],
                             "period": str(o["period"])})
    with open("experiments/n8/out_nested_transit_v1.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
    a = sum(1 for r in rows if r["stage"]=="A"); b = len(rows)-a
    print(f"stage A: {a//8} configurations   stage B: {b//8} configurations   {len(rows)} rows")
