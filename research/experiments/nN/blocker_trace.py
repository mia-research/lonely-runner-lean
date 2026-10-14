"""Per-blocker instrumentation for the flank door.  Reusable library + CLI.

For a difference set `ds` at threshold 1/n, flank `e = max ds`, openings j in [0,e):
  reading of disparity d at opening j  =  d*(n*j+1) / (n*e)   (mod 1)
  d BLOCKS j  iff  d*(n*j+1) mod n*e  is NOT in [e, (n-1)e]

This records, for EVERY blocker separately: which j it blocks, as RUNS; how many runs; the
run lengths; and the per-opening attribution (who blocked each j).  Nothing is aggregated
away -- the point is to see what each blocker does, where and when.

Theory to check against:
  * the flank itself (d = e) is never blocked
  * blocker d blocks ~d runs, each of length ~2e/(n*d), total ~2e/n
  * EVERY non-flank blocker blocks j = 0 (reading d/(n e) < 1/n whenever d < e)
"""
import math
from itertools import groupby

def blocked_js(d, e, n):
    M = n * e; lo, hi = e, (n - 1) * e
    return [j for j in range(e) if not (lo <= (d * (n * j + 1)) % M <= hi)]

def runs(js):
    """Contiguous runs of a sorted list, as (start, end) inclusive."""
    out = []
    for _, g in groupby(enumerate(js), lambda p: p[1] - p[0]):
        g = [x[1] for x in g]
        out.append((g[0], g[-1]))
    return out

def cyclic_runs(js, e):
    """Runs, merging a run ending at e-1 with one starting at 0 (the openings wrap)."""
    r = runs(js)
    if len(r) > 1 and r[0][0] == 0 and r[-1][1] == e - 1:
        r = [(r[-1][0] - e, r[0][1])] + r[1:-1]
    return r

def trace(ds, n, verbose=True):
    ds = sorted(ds); e = ds[-1]; blockers = ds[:-1]
    per = {d: blocked_js(d, e, n) for d in ds}
    union = set()
    for d in blockers: union |= set(per[d])
    survivors = [j for j in range(e) if j not in union]
    attribution = {j: [d for d in blockers if j in set(per[d])] for j in range(e)}
    if verbose:
        print(f"ds = {tuple(ds)}   n = {n}   flank e = {e}   openings 0..{e-1}")
        print(f"  flank itself (d={e}) blocked at: {per[e]}   (theory: never)")
        for d in blockers:
            r = cyclic_runs(per[d], e)
            lens = [b - a + 1 for a, b in r]
            print(f"  blocker d={d:>4}: blocks {len(per[d]):>3}/{e} openings in {len(r):>2} run(s) "
                  f"lens {lens}  pred: {d} runs of ~{2*e/(n*d):.2f}, total ~{2*e/n:.1f}")
            print(f"        runs {r}")
        print(f"  UNION blocks {len(union)}/{e};  SURVIVORS: {survivors}")
        if survivors:
            j0 = survivors[0]
            print(f"  at first survivor j={j0}: readings "
                  f"{[(d, f'{(d*(n*j0+1) % (n*e))/(n*e):.4f}') for d in ds]}")
    return per, survivors, attribution

if __name__ == "__main__":
    import sys
    print("=== sanity: the theory claims ===")
    for ds, n in [((1,2,3,4), 5), ((1,13,15,28), 5), ((1,2,3,5,6), 6), ((2,3,5,7,8,13,16), 8)]:
        per, surv, _ = trace(ds, n)
        e = max(ds)
        allblock0 = all(0 in per[d] for d in sorted(ds)[:-1])
        print(f"  -> every non-flank blocker blocks j=0? {allblock0}")
        print(f"  -> flank unblocked? {per[e] == []}")
        print()
