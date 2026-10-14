"""ok_pair_sweep_v1 -- TWO runners moved at once: how do they interact?

n = 8, individual isolation, threshold 1/8.  Base AP (1,...,8).

For each unordered pair (i,j), both runners are varied simultaneously across
their own neighbour intervals at step 0.1, with the other six holding AP
positions.  Every runner is recorded at every joint position.

Ordering is preserved: speeds stay strictly increasing in index.  A sweep never
lets one runner reach or pass another -- at equality the two coincide and the
configuration is really n = 7, and past it the set is another pair's sweep with
the labels permuted.  For non-adjacent pairs the intervals are disjoint and the
constraint binds nothing; for adjacent pairs it removes the v_i >= v_j corner.

Interval for runner m is (s_{m-1}, s_{m+1}) with s_0 = 0 (speed 0 excluded: no
stationary runner) and s_9 = 9 (the next grid position).

Recorded per runner per joint position: count, density, longest / shortest /
mean window, total per period, first isolation, and lattice occupancy.  All
durations in ORIGINAL time; period P carried in every row.

Engine and conventions as in ok_full_transit_sweep_v1 (BSM on the time axis,
fast integer path with exact fallback, individual not global).
"""
import csv, sys, os, time
from itertools import combinations
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from ok_full_transit_sweep_v1 import runner_row, INTERVALS

STEP = F(1, 10)

def grid(m):
    lo, hi = INTERVALS[m]
    out, k = [], 1
    while True:
        v = F(lo) + k * STEP
        if v >= F(hi): break
        if v > 0: out.append(v)
        k += 1
    return out

if __name__ == "__main__":
    t0 = time.time()
    AP = [F(x) for x in range(1, 9)]
    rows = []
    for (i, j) in combinations(range(1, 9), 2):
        gi, gj = grid(i), grid(j)
        n_pos = 0
        for vi in gi:
            for vj in gj:
                V = list(AP); V[i - 1] = vi; V[j - 1] = vj
                if any(V[k] >= V[k + 1] for k in range(7)):   # keep the order strict
                    continue
                recs = [runner_row(V, r) for r in range(8)]
                n_pos += 1
                for r, rec in enumerate(recs):
                    rows.append({
                        "pair": f"{i}-{j}", "mover_a": i, "mover_b": j,
                        "va": str(vi), "vb": str(vj),
                        "va_f": float(vi), "vb_f": float(vj),
                        "runner": r + 1, "speed": str(V[r]), "period": str(rec["period"]),
                        "count": rec["count"], "density": float(rec["density"]),
                        "longest": str(rec["longest"]), "longest_f": float(rec["longest"]),
                        "shortest_f": float(rec["shortest"]), "mean_f": float(rec["mean"]),
                        "first_isolation": float(rec["first"]) if rec["first"] is not None else "",
                        "on_lattice": rec["on_lattice"], "off_lattice": rec["off_lattice"],
                    })
        print(f"  pair {i}-{j}: {n_pos} joint positions   [{time.time()-t0:.0f}s]", flush=True)
    with open("experiments/n8/out_pair_sweep_v1.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
    print(f"\n{len(rows)} rows over {len(rows)//8} joint positions, {time.time()-t0:.0f}s")
