#!/usr/bin/env python3
"""m4_wide_tree_profile_v2 -- v1 for the box (1,4,5,6,6,8,15) only, stopped at level 46 to tally the window ends of
its non-leaf cells (v1 found its tree FINITE at depth 56 and so recorded no tally).  Otherwise as v1: E925 item 5(iii): the BUDGET boxes whose depth-60 rerun reached 3,000,000 nodes
again with no depth-60 cell: (1,3,4,5,6,7,13), (1,3,4,5,6,7,14) and (1,4,5,6,6,8,15) (m4_budget_stallcell_v1.jsonl;
E925 names only the first two).  The fixed-instant checker of retry3 (pin 0, cut the widest of 1..6, lowest index
on ties) run BREADTH-first, level by level, exact Fractions.  Per level: cells, leaves, non-leaf cells.  The run stops
when no non-leaf cell is left (the tree is finite; total nodes reported), at level 64, or when the frontier passes
2,000,000 cells.  At the last level reached, for a sample of 200 non-leaf cells (every k-th), the windows at the
centre with the readings nearest their ends, tallied as (lower reading, edge, upper reading, edge)."""
import sys, json
sys.path.insert(0, '.')
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from m4_fixedpoint_split_v1 import feasible, face, ONE

def kids(c):
    if feasible(c) is not None: return None
    k = max(range(1, 7), key=lambda i: (c[i][1] - c[i][0], -i))
    lo, hi = c[k]; m = (lo + hi) / 2
    a = list(c); a[k] = (lo, m); b = list(c); b[k] = (m, hi)
    return (a, b, k)

def ends(c):
    g = [(a + b) / 2 for a, b in c]
    S = feasible([(x, x) for x in g]) or []
    out = []
    for a, b in S:
        lo = None if a == 1 else min(((abs(a * x - (8 * ((a * x - 1) // 8) + 1)), i, 8 * int((a * x - 1) // 8) + 1) for i, x in enumerate(g)))[1:]
        hi = None if b == 7 else min(((abs(b * x - (8 * ((b * x + 1) // 8) - 1)), i, 8 * int((b * x + 1) // 8) - 1) for i, x in enumerate(g)))[1:]
        out.append((lo, hi))
    return out

def run(n, pool):
    faces = [face(v) for v in n]; faces[0] = (ONE, ONE)
    front = [faces]; total = 0; levels = []
    for L in range(65):
        res = pool.map(kids, front, chunksize=256)
        nl = [r for r in res if r is not None]
        cuts = Counter(r[2] for r in nl)
        total += len(front)
        levels.append({"level": L, "cells": len(front), "leaves": len(front) - len(nl), "nonleaf": len(nl), "cut_coord": dict(sorted(cuts.items()))})
        print(json.dumps({"n": n, **levels[-1]}), flush=True)
        if not nl:
            return {"n": n, "status": "FINITE", "total_nodes": total, "depth": L}
        nxt = [x for r in nl for x in r[:2]]
        if len(nxt) > 2000000 or L == 46:
            step = max(1, len(nl) // 200)
            samp = [nl_c for nl_c in [front[i] for i, r in enumerate(res) if r is not None][::step]][:200]
            tally = Counter()
            for e in pool.map(ends, samp):
                for w in e: tally[str(w)] += 1
            return {"n": n, "status": "STOPPED", "at_level": L, "next_frontier": len(nxt), "total_nodes_so_far": total,
                    "window_ends_in_sample": dict(tally.most_common(30))}
        front = nxt

if __name__ == "__main__":
    with Pool(6) as pool:
        for n in ([1, 4, 5, 6, 6, 8, 15],):
            print(json.dumps(run(n, pool)), flush=True)
