"""ok_r8_integer_law_v1 -- (1,2,3,4,5,6,7,x) for integer x, r1..r7 never move.

n = 8, individual isolation, threshold 1/8.  The grid structure lives at integers,
so only integers are tested.  With k = floor(x/8) and r = x mod 8:

  R1  r8's first isolation = 1 / (8 (x - 7))          the d_min rule
  R2  r8's tally at coverage = k
  R3  coverage = 1/8                    if r = 0      (the configuration is a grid)
               = 1/8 + 1/(64 k)         otherwise
  R4  the only delayed runner is r_r, the residue partner; r1..r7 otherwise at 1/8

Verified exact for every integer x from 8 to 160: 153 configurations, 0 violations.

Consequence: as x grows the non-grid penalty 1/(64k) vanishes, so coverage tends
to 1/8 from above.  Pushing r8 far away makes the residue collision asymptotically
harmless, while r8 itself collects k turns before the pack gets one.
"""
import sys, os, csv
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from ok_full_transit_sweep_v1 import runner_row

BASE = [F(i) for i in range(1, 8)]

def measure(x):
    V = BASE + [F(x)]
    recs = [runner_row(V, i) for i in range(8)]
    P = recs[0]["period"]
    ms = [r["windows"][0][0] for r in recs]
    cov = max(ms)
    reps = int(cov / P); rem = cov - reps * P
    tally8 = sum(1 for a, b in recs[7]["windows"] if a <= rem) + reps * recs[7]["count"]
    return {"x": x, "k": x // 8, "r": x % 8, "grid": x % 8 == 0,
            "r8_moment": ms[7], "r8_tally": tally8, "coverage": cov,
            "delayed": [i + 1 for i in range(7) if ms[i] != F(1, 8)]}

def predict(x):
    k, r = x // 8, x % 8
    return {"r8_moment": F(1, 8) / (F(x) - 7), "r8_tally": k,
            "coverage": F(1, 8) if r == 0 else F(1, 8) + F(1, 64 * k),
            "delayed": [] if r == 0 else [r]}

if __name__ == "__main__":
    rows, bad = [], 0
    for x in range(8, 161):
        m, p = measure(x), predict(x)
        ok = all(m[key] == p[key] for key in p)
        bad += not ok
        rows.append({**{k: str(v) for k, v in m.items()}, "rules_hold": ok})
    with open("experiments/n8/out_r8_integer_law_v1.csv", "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
    print(f"x = 8..160: {len(rows)} configurations, {bad} violations")
