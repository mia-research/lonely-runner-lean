"""ok_ap_transit_r1_r2_v1 -- isolation times of ALL runners along two AP transits.

n = 8, individual isolation, threshold 1/8.

  Transit A: base AP (1,...,8), r1 moves over [1, 2)   -- toward its upper neighbour.
  Transit B: base AP (1,...,8), r2 moves over (1, 3)   -- across both its neighbours.

At every position, for every runner, record the isolation windows themselves:
count, each width, the total isolated time per period, the density, the longest
and shortest window, and the first isolation time.

Conventions this script is built to respect.

  BSM on the time axis.  Boundary points and open-cell midpoints are evaluated
  separately, so isolated witnesses (gap exactly 1/8) are not lost.  At the AP
  the end runners' good sets ARE four isolated points; a midpoint-only test
  reports them as empty.

  ORIGINAL time, not scaled.  Reducing a configuration whose moved speed has
  denominator q stretches the period by ~q.  Window counts and widths taken in
  the reduced configuration's own time are not comparable across positions, so
  every window here is mapped back: period P = L/g in original time, and each
  reduced window is scaled by P.

  Denominator is reported, never concealed.  A uniform step of 1/100 visits only
  denominators dividing 100, and those are the small-denominator points where
  counts are lowest.  The denominator of each position is carried in the output
  so the effect is visible in the data rather than hidden by the axis.

  No runner is given speed 0 and no runner is adjoined; the moved runner's
  endpoints are excluded where they would duplicate another speed.

Exact throughout: rational endpoints, integer comparisons.
"""
import csv, sys
from fractions import Fraction as F
from math import gcd
from functools import reduce

N = 8

def multipliers(speeds, i):
    """Integer constraint multipliers for runner i and the original-time period."""
    ds = [abs(speeds[i] - v) for j, v in enumerate(speeds) if j != i]
    if any(d == 0 for d in ds):
        return None, None
    L = reduce(lambda a, b: a * b // gcd(a, b), [d.denominator for d in ds], 1)
    D = [int(d * L) for d in ds]
    g = reduce(gcd, D)
    return sorted(d // g for d in D), F(L, g)

def _ok(mult, num, den):
    """||m * num/den|| >= 1/N, in integers."""
    for m in mult:
        r = (m * num) % den
        if 8 * min(r, den - r) < den:
            return False
    return True

def windows(mult):
    """Maximal components of {s in [0,1) : ||m s|| >= 1/N for all m}. Exact, BSM."""
    pts = {F(0)}
    for m in mult:
        base = N * m
        for k in range(m + 1):
            for t in (N * k + 1, N * k - 1):
                if 0 <= t < base:
                    pts.add(F(t, base))
    pts = sorted(pts)
    segs = []
    for idx, a in enumerate(pts):
        if _ok(mult, a.numerator, a.denominator):          # boundary point
            segs.append((a, a))
        b = pts[idx + 1] if idx + 1 < len(pts) else F(1)
        if b > a:
            mnum = a.numerator * b.denominator + b.numerator * a.denominator
            mden = 2 * a.denominator * b.denominator
            if _ok(mult, mnum, mden):                      # open cell
                segs.append((a, b))
    merged = []
    for s in segs:
        if merged and s[0] <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], s[1]))
        else:
            merged.append(s)
    return merged

def record(speeds, i):
    mult, P = multipliers(speeds, i)
    if mult is None:
        return None
    w = windows(mult)
    wins = [(a * P, b * P) for a, b in w]                  # ORIGINAL time
    widths = [b - a for a, b in wins]
    return {"period": P, "count": len(w), "windows": wins, "widths": widths,
            "total": sum(widths), "density": sum(b - a for a, b in w),
            "longest": max(widths) if widths else F(0),
            "shortest": min(widths) if widths else F(0),
            "first": wins[0][0] if wins else None}

def transit(base, idx, lo, hi, step, label, detail_q=20):
    """Move runner idx over (lo,hi) at the given step. Endpoints that duplicate
    another speed are skipped; a position equal to the runner's own AP value is
    kept (it is the reference)."""
    rows, details = [], []
    k = 0
    while True:
        v = F(lo) + k * step
        k += 1
        if v >= F(hi):
            break
        sp = list(base); sp[idx] = v
        if len(set(sp)) < 8:
            continue
        recs = [record(sp, i) for i in range(8)]
        if any(r is None for r in recs):
            continue
        for i, r in enumerate(recs):
            rows.append({
                "transit": label, "moved": idx + 1, "r": str(v),
                "r_float": float(v), "q": v.denominator,
                "runner": i + 1, "speed": str(sp[i]), "period": str(r["period"]),
                "count": r["count"], "total_isolated": str(r["total"]),
                "total_float": float(r["total"]), "density": float(r["density"]),
                "longest": str(r["longest"]), "longest_float": float(r["longest"]),
                "shortest_float": float(r["shortest"]),
                "first_isolation": float(r["first"]) if r["first"] is not None else "",
            })
            if v.denominator <= detail_q:
                for (a, b) in r["windows"]:
                    details.append({"transit": label, "r": str(v), "runner": i + 1,
                                    "start": str(a), "end": str(b),
                                    "start_float": float(a), "end_float": float(b),
                                    "width_float": float(b - a)})
        print(f"  {label} r={str(v):>8} q={v.denominator:>3} "
              f"counts={[r['count'] for r in recs]} "
              f"min_dens={float(min(r['density'] for r in recs)):.5f} "
              f"min_longest={float(min(r['longest'] for r in recs)):.6f}", flush=True)
    return rows, details

if __name__ == "__main__":
    step = F(1, 100)
    AP = [F(x) for x in range(1, 9)]
    allrows, alldet = [], []
    print("TRANSIT A: r1 over [1,2), step 1/100")
    a, d = transit(AP, 0, 1, 2, step, "A_r1")
    allrows += a; alldet += d
    print("TRANSIT B: r2 over (1,3), step 1/100")
    b, d2 = transit(AP, 1, F(101, 100), 3, step, "B_r2")
    allrows += b; alldet += d2
    with open("experiments/n8/out_ap_transit_r1_r2_v1.csv", "w", newline="") as f:
        wr = csv.DictWriter(f, fieldnames=list(allrows[0].keys())); wr.writeheader(); wr.writerows(allrows)
    with open("experiments/n8/out_ap_transit_windows_v1.csv", "w", newline="") as f:
        wr = csv.DictWriter(f, fieldnames=list(alldet[0].keys())); wr.writeheader(); wr.writerows(alldet)
    print(f"\nwrote {len(allrows)} summary rows, {len(alldet)} window rows")
