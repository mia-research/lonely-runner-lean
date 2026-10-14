"""Replication of ok_full_transit_sweep_v1 (DISTURBANCE_RULE_v1), recording positions.

Same sweep: base AP (1,...,8); each runner m moved across its open neighbour interval in steps of 0.01, all others
at AP positions.  Same engine: BSM windows from ok_full_transit_sweep_v1 (get_windows, multipliers), unchanged.

New: at the START of every runner's first isolation window, record for all eight runners
  pos     track position relative to the subject, in eighths  (8 * frac((v_j - v_i) t))
  shift   (v_j - AP_j) * t in eighths  -- how far each runner sits from its AP position at that instant
  order   cyclic track order (labels 1..8), the runners behind/ahead (ties kept), both gaps, which gap = 1/8
  lattice 8t, and whether t is an odd eighth (an AP global instant)
Written to out_full_transit_positions_v2.csv; a summary is printed."""
import csv, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from math import floor
from collections import Counter, defaultdict
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from ok_full_transit_sweep_v1 import get_windows, multipliers, INTERVALS
AP = [F(x) for x in range(1, 9)]
def fr(x): return x - floor(x)
def first_time(V, i):
    mult, P = multipliers(V, i)
    w = get_windows(mult)
    return w[0][0] * P if w else None
def snapshot(V, i, t):
    rel = {j: fr((V[j] - V[i]) * t) for j in range(8)}
    order = sorted(range(8), key=lambda j: (rel[j], j))
    others = [j for j in range(8) if j != i]
    ahead_d = min(rel[j] for j in others); behind_d = max(rel[j] for j in others)
    ahead = [j + 1 for j in others if rel[j] == ahead_d]; behind = [j + 1 for j in others if rel[j] == behind_d]
    gap_behind, gap_ahead = 1 - behind_d, ahead_d
    setter = ("behind" if gap_behind == F(1, 8) else "") + ("ahead" if gap_ahead == F(1, 8) else "")
    eight_t = 8 * t
    ap_instant = eight_t.denominator == 1 and eight_t.numerator % 2 == 1
    steps = Counter()
    seq = [j for j in order]
    for k in range(8):
        a, b = seq[k], seq[(k + 1) % 8]
        d = (b - a) % 8; steps[min(d, 8 - d)] += 1
    return dict(pos=[str(8 * rel[j]) for j in range(8)], shift=[str(8 * (V[j] - AP[j]) * t) for j in range(8)],
                order=[j + 1 for j in order], behind=behind, ahead=ahead, gap_behind=str(gap_behind), gap_ahead=str(gap_ahead),
                setter=setter or "none", eight_t=str(eight_t), ap_instant=ap_instant,
                ap_order=("step-1" if steps[1] == 8 else "step-3" if steps[3] == 8 else "other"),
                ties=len(set(rel.values())) < 8)
if __name__ == "__main__":
    rows = []
    for m, (lo, hi) in INTERVALS.items():
        for num in range(lo * 100 + 1, hi * 100):
            V = list(AP); V[m - 1] = F(num, 100)
            if len(set(V)) < 8 or V[0] <= 0: continue
            for i in range(8):
                t = first_time(V, i)
                s = snapshot(V, i, t)
                role = "mover" if i == m - 1 else ("disturbed" if t != F(1, 8) else "untouched")
                rows.append(dict(mover=m, r=str(V[m - 1]), direction=("up" if V[m - 1] > AP[m - 1] else "down"),
                                 runner=i + 1, t=str(t), role=role, **s))
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out_full_transit_positions_v2.csv")
    with open(out, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys())); w.writeheader()
        for r in rows: w.writerow({k: (" ".join(map(str, v)) if isinstance(v, list) else v) for k, v in r.items()})
    print(f"{len(rows)} runner-rows written to {os.path.basename(out)}")
    # summary
    print("\nroles (untouched = time exactly 1/8):", dict(Counter(r["role"] for r in rows)))
    for role in ("untouched", "disturbed", "mover"):
        R = [r for r in rows if r["role"] == role]
        print(f"\n[{role}] {len(R)}")
        print("   time is an odd eighth (AP instant):", dict(Counter(r["ap_instant"] for r in R)))
        print("   track order is the AP event order:", dict(Counter(r["ap_order"] for r in R)))
        print("   gap exactly 1/8 at the start of the window:", dict(Counter(r["setter"] for r in R)))
        print("   ties on the track:", dict(Counter(r["ties"] for r in R)))
    print("\ndisturbed runners, by mover and direction: (runner, time, behind|ahead, which gap = 1/8, AP order) for the 3 positions nearest the AP")
    by = defaultdict(list)
    for r in rows:
        if r["role"] != "untouched": by[(r["mover"], r["direction"])].append(r)
    for (m, d), R in sorted(by.items()):
        pts = sorted({r["r"] for r in R}, key=lambda x: abs(F(x) - AP[m - 1]))[:1]
        sel = [r for r in R if r["r"] in pts]
        print(f"  r{m} {d:>4} (r{m}={pts[0]}): " + "; ".join(
            f"r{r['runner']}[{r['role'][0]}] t={r['t']} {'/'.join(map(str,r['behind']))}|{'/'.join(map(str,r['ahead']))} {r['setter']} {r['ap_order']}" for r in sel))
