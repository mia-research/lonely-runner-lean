"""ok_service_disparity_v1 -- how unequally is loneliness shared out?

n = 8, individual isolation, threshold 1/8.  Base AP (1,...,8).  Each runner in
turn is transited across its neighbour interval (step 0.1) with the others held
at AP positions.

For each configuration, run the clock to the COVERAGE TIME -- the first moment at
which every runner has been lonely at least once -- and count how many isolation
windows each runner has had by then.  Windows repeat with the period, so full
periods are counted as repeats plus the partial tail.

At the AP every runner is served once, at the same instant: tally 1,1,...,1.
Any displacement turns that into a queue.  This measures the queue.
"""
import csv, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from ok_full_transit_sweep_v1 import runner_row, INTERVALS

STEP = F(1, 10)

def tallies(V):
    recs = [runner_row(V, i) for i in range(8)]
    if any(not r["windows"] for r in recs): return None, None, None
    P = recs[0]["period"]
    tstar = max(r["windows"][0][0] for r in recs)
    out = []
    for r in recs:
        reps = int(tstar / P)
        rem = tstar - reps * P
        out.append(sum(1 for a, b in r["windows"] if a <= rem) + reps * r["count"])
    return tstar, out, [i+1 for i,r in enumerate(recs) if r["windows"][0][0]==tstar]

if __name__ == "__main__":
    AP = [F(x) for x in range(1, 9)]
    rows = []
    for m, (lo, hi) in INTERVALS.items():
        print(f"\n--- r{m} transiting ({lo},{hi}) ---")
        print(f"  {'speed':>6} {'coverage':>9} {'tallies r1..r8':>32} {'max':>4} {'min':>4} "
              f"{'ratio':>6} {'last served':>12}")
        v = F(lo) + STEP
        while v < F(hi):
            V = list(AP); V[m-1] = v
            if v > 0 and len(set(V)) == 8:
                t, tal, last = tallies(V)
                if t is not None:
                    ratio = max(tal)/max(1, min(tal))
                    star = "  <- AP" if v == F(m) else ""
                    print(f"  {str(v):>6} {float(t):>9.4f} {str(tal):>32} {max(tal):>4} "
                          f"{min(tal):>4} {ratio:>6.1f} {str(['r'+str(x) for x in last]):>12}{star}")
                    rows.append({"mover": m, "speed": str(v), "coverage": float(t),
                                 "tallies": " ".join(map(str, tal)), "max": max(tal),
                                 "min": min(tal), "ratio": round(ratio,3),
                                 "last_served": " ".join('r'+str(x) for x in last)})
            v += STEP
    with open("experiments/n8/out_service_disparity_v1.csv","w",newline="") as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
    print(f"\n{len(rows)} configurations written")
