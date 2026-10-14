"""ok_full_transit_sweep_v1 -- every runner swept across its whole neighbour interval.

n = 8, individual isolation, threshold 1/8.  Base AP (1,...,8).

For each runner m in turn, m is varied across the OPEN interval between its two
neighbours while all seven others hold their AP positions:

    r1: 0.01 .. 1.99      r5: 4.01 .. 5.99
    r2: 1.01 .. 2.99      r6: 5.01 .. 6.99
    r3: 2.01 .. 3.99      r7: 6.01 .. 7.99
    r4: 3.01 .. 4.99      r8: 7.01 .. 8.99

step 0.01.  Endpoints excluded: a speed equal to a neighbour's is a duplicate
runner, and speed 0 is excluded outright (no stationary runner -- translation is
free, adjoining is not).

At every position, EVERY runner is recorded, individually:

  isolation TIMES     first isolation; each window's start and end; how many
                      windows sit on the eighth-lattice {m/8} and how many have
                      drifted off it; distance to the lattice for those off it.
  isolation DURATION  longest window, shortest, mean, total isolated time per
                      period, and density (= total / period).

Durations are in ORIGINAL time.  Reducing a configuration whose moved speed has
denominator q stretches the period by ~q, so a duration read off the reduced
configuration is not comparable across positions.  Period P is carried in every
row so total-per-period is never read as if it were comparable; density and the
individual window widths are the comparable quantities.

Individual isolation, not global: each runner's constraint set is its own seven
differences.  Global would use all 28 pairs and give all eight runners the same
good set.

BSM on the time axis: boundary points and open-cell midpoints evaluated
separately, so isolated witnesses (gap exactly 1/8) survive -- at the AP the end
runners' good sets ARE four such points.

Two engines run: an integer-scaled fast path, and the exact Fraction path from
ok_ap_transit_r1_r2_v1.  The fast path is used only where its overflow guard
passes, and the two are checked against each other on a sample before the sweep
proceeds.  Disagreement is a hard stop.
"""
import csv, sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from math import gcd
from functools import reduce
from ok_ap_transit_r1_r2_v1 import multipliers, windows as windows_exact

N = 8
LIMIT = 1 << 62

def windows_fast(mult):
    """Integer-scaled BSM over the common denominator D = 8*lcm(mult).
    Returns None when D would overflow int64 territory -- caller falls back."""
    L = reduce(lambda a, b: a * b // gcd(a, b), mult, 1)
    D = 8 * L
    if max(mult) * 2 * D > LIMIT:
        return None
    pts = {0}
    for m in mult:
        step = D // m; off = step // 8
        for k in range(m + 1):
            for t in (k * step + off, k * step - off):
                if 0 <= t < D: pts.add(t)
    pts = sorted(pts)
    def ok(num, den):
        for m in mult:
            r = (m * num) % den
            if 8 * min(r, den - r) < den: return False
        return True
    segs = []
    for i, a in enumerate(pts):
        if ok(a, D): segs.append((2 * a, 2 * a))
        b = pts[i + 1] if i + 1 < len(pts) else D
        if b > a and ok(a + b, 2 * D): segs.append((2 * a, 2 * b))
    merged = []
    for s in segs:
        if merged and s[0] <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], s[1]))
        else: merged.append(s)
    return [(F(a, 2 * D), F(b, 2 * D)) for a, b in merged]

def get_windows(mult):
    w = windows_fast(mult)
    return windows_exact(mult) if w is None else w

def runner_row(V, i):
    mult, P = multipliers(V, i)
    w = get_windows(mult)
    wins = [(a * P, b * P) for a, b in w]
    widths = [b - a for a, b in wins]
    on = off = 0; dmin = None
    for (a, b) in wins:
        if (b * 8).__floor__() >= (a * 8).__ceil__(): on += 1
        else:
            off += 1
            m = (a * 8).__floor__()
            d = min(abs(a - F(m, 8)), abs(b - F(m + 1, 8)))
            dmin = d if dmin is None or d < dmin else dmin
    n = len(wins)
    return {
        "period": P, "count": n, "windows": wins,
        "total": sum(widths, F(0)), "density": sum((b - a for a, b in w), F(0)),
        "longest": max(widths) if widths else F(0),
        "shortest": min(widths) if widths else F(0),
        "mean": (sum(widths, F(0)) / n) if n else F(0),
        "first": wins[0][0] if wins else None,
        "on_lattice": on, "off_lattice": off, "min_off_dist": dmin,
    }

INTERVALS = {1: (0, 2), 2: (1, 3), 3: (2, 4), 4: (3, 5),
             5: (4, 6), 6: (5, 7), 7: (6, 8), 8: (7, 9)}

def selfcheck(n=60):
    """Fast path vs exact path.  Hard stop on any disagreement."""
    AP = [F(x) for x in range(1, 9)]
    checked = fell_back = 0
    for m, (lo, hi) in INTERVALS.items():
        for num in range(lo * 100 + 1, hi * 100, max(1, (hi - lo) * 100 // 8)):
            V = list(AP); V[m - 1] = F(num, 100)
            if len(set(V)) < 8: continue
            for i in range(8):
                mult, P = multipliers(V, i)
                f = windows_fast(mult)
                if f is None: fell_back += 1; continue
                if f != windows_exact(mult):
                    raise SystemExit(f"DISAGREEMENT mover r{m} r={F(num,100)} runner {i+1}")
                checked += 1
                if checked >= n: 
                    print(f"  self-check: {checked} agreements, 0 disagreements, "
                          f"{fell_back} fell back to exact"); return
    print(f"  self-check: {checked} agreements, 0 disagreements, {fell_back} fell back")

if __name__ == "__main__":
    t0 = time.time()
    print("self-check (fast path vs exact path)...", flush=True)
    selfcheck()
    AP = [F(x) for x in range(1, 9)]
    rows, wins_rows = [], []
    for m, (lo, hi) in INTERVALS.items():
        n_pos = 0
        for num in range(lo * 100 + 1, hi * 100):
            v = F(num, 100)
            V = list(AP); V[m - 1] = v
            if len(set(V)) < 8 or v <= 0: continue
            recs = [runner_row(V, i) for i in range(8)]
            n_pos += 1
            for i, r in enumerate(recs):
                rows.append({
                    "mover": m, "r": str(v), "r_float": float(v), "q": v.denominator,
                    "runner": i + 1, "speed": str(V[i]), "period": str(r["period"]),
                    "count": r["count"],
                    "density": float(r["density"]),
                    "total_per_period": float(r["total"]),
                    "longest": str(r["longest"]), "longest_f": float(r["longest"]),
                    "shortest_f": float(r["shortest"]), "mean_f": float(r["mean"]),
                    "first_isolation": float(r["first"]) if r["first"] is not None else "",
                    "on_lattice": r["on_lattice"], "off_lattice": r["off_lattice"],
                    "min_off_dist": float(r["min_off_dist"]) if r["min_off_dist"] is not None else "",
                })
                if v.denominator <= 20:
                    for (a, b) in r["windows"]:
                        wins_rows.append({"mover": m, "r": str(v), "runner": i + 1,
                                          "start": str(a), "end": str(b),
                                          "start_f": float(a), "width_f": float(b - a)})
        print(f"  r{m} over ({lo},{hi}): {n_pos} positions   [{time.time()-t0:.0f}s]", flush=True)
    with open("experiments/n8/out_full_sweep_v1.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
    with open("experiments/n8/out_full_sweep_windows_v1.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(wins_rows[0].keys())); w.writeheader(); w.writerows(wins_rows)
    print(f"\n{len(rows)} rows, {len(wins_rows)} window rows, {time.time()-t0:.0f}s")
