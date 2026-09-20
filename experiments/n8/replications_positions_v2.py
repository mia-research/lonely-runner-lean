"""Replications with positions recorded (same BSM engine, same snapshot as full_transit_positions_v2):
  R1  r8 from 8 to 16.9, step 0.1   (R8_TO_NEXT_GRID_v1)
  R2  every pair of runners moved together, step 0.1 on each neighbour interval   (ok_pair_sweep_v1 grid)"""
import csv, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from itertools import combinations
from collections import Counter, defaultdict
from multiprocessing import Pool
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from full_transit_positions_v2 import first_time, snapshot, AP
    from ok_pair_sweep_v1 import grid
def conf_rows(args):
    tag, V, movers = args
    out = []
    for i in range(8):
        t = first_time(V, i); s = snapshot(V, i, t)
        role = "mover" if (i + 1) in movers else ("disturbed" if t != F(1, 8) else "untouched")
        out.append(dict(test=tag, V=" ".join(map(str, V)), movers=" ".join(map(str, movers)), runner=i + 1, t=str(t), role=role, **s))
    return out
def summary(name, rows):
    print(f"\n=== {name}: {len(rows)} runner-rows")
    for role in ("untouched", "disturbed", "mover"):
        R = [r for r in rows if r["role"] == role]
        if not R: continue
        print(f"  [{role}] {len(R)}: AP instant {dict(Counter(r['ap_instant'] for r in R))}; "
              f"track order {dict(Counter(r['ap_order'] for r in R))}; gap at 1/8 {dict(Counter(r['setter'] for r in R))}; "
              f"ties {dict(Counter(r['ties'] for r in R))}")
if __name__ == "__main__":
    jobs = []
    for k in range(81, 170):
        V = AP[:7] + [F(k, 10)]; jobs.append(("R1", V, (8,)))
    for a, b in combinations(range(1, 9), 2):
        for va in grid(a):
            for vb in grid(b):
                V = list(AP); V[a - 1] = va; V[b - 1] = vb
                if all(V[j] < V[j + 1] for j in range(7)) and V[0] > 0: jobs.append(("R2", V, (a, b)))
    with Pool(8) as p: res = p.map(conf_rows, jobs, chunksize=16)
    rows = [x for r in res for x in r]
    out = os.path.join(os.path.dirname(os.path.abspath(__file__)), "out_replications_positions_v2.csv")
    with open(out, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys())); w.writeheader()
        for r in rows: w.writerow({k: (" ".join(map(str, v)) if isinstance(v, list) else v) for k, v in r.items()})
    R1 = [r for r in rows if r["test"] == "R1"]; R2 = [r for r in rows if r["test"] == "R2"]
    summary("R1 r8 from 8.1 to 16.9", R1)
    print("  R1 integer and half-integer positions: disturbed runners (runner, t, behind|ahead, order)")
    for k in range(81, 170):
        if k % 5: continue
        Rs = [r for r in R1 if r["V"].split()[7] == str(F(k, 10)) and r["role"] != "untouched"]
        print(f"   r8={F(k,10)}: " + "; ".join(f"r{r['runner']} t={r['t']} {'/'.join(map(str,r['behind']))}|{'/'.join(map(str,r['ahead']))} {r['ap_order']}" for r in Rs))
    summary("R2 two movers", R2)
    # which runners are disturbed: the approached neighbour of either mover?
    by = defaultdict(dict)
    for r in R2: by[r["V"]][int(r["runner"])] = r
    c = Counter()
    for Vs, R in by.items():
        V = [F(x) for x in Vs.split()]; movers = [int(x) for x in R[1]["movers"].split()]
        approached = set()
        for m in movers:
            d = V[m - 1] - AP[m - 1]
            nb = m + 1 if d > 0 else m - 1
            if 1 <= nb <= 8: approached.add(nb)
            if m == 8 and d > 0: approached.add(1)
            if m == 1 and d < 0: approached.add(8)
        for i, r in R.items():
            if r["role"] == "mover": continue
            c[("approached by a mover" if i in approached else "not approached", r["role"])] += 1
    print("  R2 non-movers: (approached by a mover?, role):", dict(sorted(c.items())))
