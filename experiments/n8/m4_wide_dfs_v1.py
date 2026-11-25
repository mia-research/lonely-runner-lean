#!/usr/bin/env python3
"""m4_wide_dfs_v1 -- does the retry3 fixed-instant checker terminate on (1,3,4,5,6,7,13) and (1,3,4,5,6,7,14)?
(m4_wide_tree_profile_v1 stopped them at the 2,000,000-cell frontier cap at levels 49 and 48; the third wide box,
(1,4,5,6,6,8,15), is FINITE at depth 56.)  The same checker (pin 0, widest of 1..6, lowest index on ties, exact
Fractions), split breadth-first at level 24 into subtrees, each run depth-first to completion with a depth cap of
120 (a cell at depth 120 is reported as STALL with the cell).  No node budget.  Output per box: total nodes, leaves,
maximum depth, STALL cells."""
import sys, json, time
sys.path.insert(0, '.')
from fractions import Fraction as F
from multiprocessing import Pool
from m4_fixedpoint_split_v1 import feasible, face, ONE

def kids(c):
    if feasible(c) is not None: return None
    k = max(range(1, 7), key=lambda i: (c[i][1] - c[i][0], -i))
    lo, hi = c[k]; m = (lo + hi) / 2
    a = list(c); a[k] = (lo, m); b = list(c); b[k] = (m, hi)
    return (a, b)

def sub(arg):
    c0, d0 = arg
    st = [(c0, d0)]; N = L = 0; D = 0
    while st:
        c, d = st.pop(); N += 1
        r = kids(c)
        if r is None: L += 1; D = max(D, d); continue
        if d >= 120: return {"N": N, "L": L, "D": d, "stall": [[str(a), str(b)] for a, b in c]}
        st += [(r[0], d + 1), (r[1], d + 1)]
    return {"N": N, "L": L, "D": D, "stall": None}

if __name__ == "__main__":
    with Pool(int(sys.argv[1]) if len(sys.argv) > 1 else 4) as pool:
        for n in ([1, 3, 4, 5, 6, 7, 13], [1, 3, 4, 5, 6, 7, 14]):
            t0 = time.time()
            faces = [face(v) for v in n]; faces[0] = (ONE, ONE)
            front = [faces]; N = L = 0
            for lev in range(24):
                res = pool.map(kids, front, chunksize=64)
                N += len(front); L += sum(r is None for r in res)
                front = [x for r in res if r is not None for x in r]
            tot = {"N": N, "L": L, "D": 0, "stalls": 0}; first = None; done = 0
            for r in pool.imap_unordered(sub, [(c, 24) for c in front], chunksize=1):
                tot["N"] += r["N"]; tot["L"] += r["L"]; tot["D"] = max(tot["D"], r["D"]); done += 1
                if r["stall"]: tot["stalls"] += 1; first = first or r["stall"]
                if done % 200 == 0:
                    print(json.dumps({"n": n, "progress": "%d/%d subtrees" % (done, len(front)), **tot, "s": round(time.time() - t0)}), flush=True)
            print(json.dumps({"n": n, "status": "FINITE" if tot["stalls"] == 0 else "STALL", "subtrees": len(front), **tot,
                              "first_stall": first, "s": round(time.time() - t0)}), flush=True)
